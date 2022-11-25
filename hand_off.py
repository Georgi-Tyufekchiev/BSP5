"""
Implementation of the Hand-off Phase
"""
import sys
from time import perf_counter as cnt
from py_ecc import optimized_bls12_381 as curve

from KZG import *
from SSS import SSS
from utils import *


class Handoff:
    """
        Class for the Hand-off phase
    """
    oValidations = []
    nValidations = []
    commit = {}

    def __init__(self):
        """
        Initialise the (k,n) Shamir secret sharing scheme along with the Trusted Setup, which will create the PK
        """
        self.PARTIES = 10
        self.THRESHOLD = 4
        self.sss = SSS(self.PARTIES, self.THRESHOLD)
        self.__setup = generate_setup(1927409816240961209460912649124, self.THRESHOLD)

    @staticmethod
    def __eval(f, h, x):
        fx = eval_poly_at(f, x)
        hx = eval_poly_at(h, x)
        return fx, hx

    def distribution(self):
        """
         Protocol 3 "Distribution"
        """
        # committee = { 1 :(([poly1],[poly2]), ([poly3],[poly4]), ([shares1],[shares2]), ([shares3],[shares4]))}
        # STEP 1: Create the coupled sharing for each Pi i.e (u,u~) and (v,v~)
        tic = cnt()
        committee = {}
        print("PROTOCOL 3 DISTRIBUTION:")
        for i in range(self.PARTIES):
            committee[i] = self.sss.coupledSharing()
        toc = cnt()
        print(f"Coupled sharing in {(toc - tic) / self.PARTIES:0.6f} seconds per party")
        # STEP 2: Compute the commitment of (u,v) and (u~,v~) for each Pi
        tic = cnt()
        for i in range(self.PARTIES):
            # extract tuple = (poly1, poly2)
            uPoly = committee[i][0]
            vPoly = committee[i][1]
            self.commit[i] = (commit_to_poly(uPoly[0], vPoly[0], self.__setup),
                              commit_to_poly(uPoly[1], vPoly[1], self.__setup))
        toc = cnt()
        print(f"Committing to polynomials in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        # Create the witness for (u,v) and (u~,v~) for each Pi
        proof = {}
        # TODO: MAKE HASH (PK,C)
        x1 = {}
        x2 = {}
        for i in range(self.PARTIES):
            hashing1 = fsh(self.__setup, self.commit[i][0])
            hashing2 = fsh(self.__setup, self.commit[i][1])
            x1[i] = [int.from_bytes(hashing1.read(j + 1), byteorder='big') for j in range(self.PARTIES)]
            x2[i] = [int.from_bytes(hashing2.read(j + 1), byteorder='big') for j in range(self.PARTIES)]

        tic = cnt()

        # The final dictionary looks like
        # {Party : ( {x_i:(w_i,f(x_i),h(x_i)}, {x_i:(w_iTilde,f~(x_i),h~(x_i))} )}
        # First Each party evaluates the polynomials at a random point x
        # Each party make the tuple (proof, f(x), h(x)) -> this will be given to the old committee
        # The steps above are done again but for the new committee with different polynomials
        print("Each Party i will compute the witness for every Party j - O(n^2)")
        for i in range(self.PARTIES):
            uPoly = committee[i][0]
            vPoly = committee[i][1]
            x1i = x1[i]
            x2i = x2[i]
            for j in range(self.PARTIES):
                polyEvals = self.__eval(uPoly[0], vPoly[0], x1i[j])
                polyTildeEvals = self.__eval(uPoly[1], vPoly[1], x2i[j])
                proof[i] = (
                    {
                        x1i[j]: (
                            compute_proof_single(uPoly[0], vPoly[0], x1i[j], self.__setup),
                            polyEvals[0],
                            polyEvals[1]
                        )
                    },
                    {
                        x2i[j]: (
                            compute_proof_single(uPoly[1], vPoly[1], x2i[j], self.__setup),
                            polyTildeEvals[0],
                            polyTildeEvals[1]
                        )
                    }
                )

        toc = cnt()
        print(f"Proofs done in {(toc - tic) / self.PARTIES:0.6f} seconds per Party i")

        # For each Pj in Old Committee, Pi sends Pj the j-th share of (u,v) and the (x,proof,f(x),h(x))
        # For each Pj in New Committee, Pi sends Pj the j-th share of (u~,v~) and the (x,proof~,f~(x),h~(x))
        oldCommittee = {}
        newCommittee = {}
        tic = cnt()
        print("Starting distribution - O(n^2)")
        for i in range(self.PARTIES):
            uShares = committee[i][2][0]
            vShares = committee[i][3][0]

            uTilde = committee[i][2][1]
            vTilde = committee[i][3][1]

            # for each witness extract the following: [x,(proof,f(x),h(x))]
            witness = proof[i][0].items()
            witnessTilde = proof[i][1].items()
            for j in range(self.PARTIES):
                if j not in oldCommittee:
                    oldCommittee[j] = ([uShares[j]], [vShares[j]], [witness])
                else:
                    oldCommittee[j][0].append(uShares[j])
                    oldCommittee[j][1].append(vShares[j])
                    oldCommittee[j][2].append(witness)

                if j not in newCommittee:
                    newCommittee[j] = ([uTilde[j]], [vTilde[j]], [witnessTilde])
                else:
                    newCommittee[j][0].append(uTilde[j])
                    newCommittee[j][1].append(vTilde[j])
                    newCommittee[j][2].append(witnessTilde)

        toc = cnt()
        print(f"Distribute done in {(toc - tic) / self.PARTIES:0.6f} seconds per party i")

        # Each Pi in old/new committee executes VerifyPoly to validate the shares and the witness
        tic = cnt()
        print("Starting validation - O(n^2)")
        for i in range(self.PARTIES):
            for j in range(self.PARTIES):
                witness = oldCommittee[i][2][j]
                xi, witnessTup = list(witness)[0]
                w, fx, hx = witnessTup
                oCommit = self.commit[j][0]

                if not check_proof_single(oCommit, w, xi, fx, hx, self.__setup):
                    print("Validation BAD FOR OLD %d %d" % (i, j))
                    self.oValidations.append((j, witness, oCommit))

                nCommit = self.commit[j][1]
                witness = newCommittee[i][2][j]
                xi, witnessTup = list(witness)[0]
                w, fx, hx = witnessTup
                if not check_proof_single(nCommit, w, xi, fx, hx, self.__setup):
                    print("Validation BAD FOR NEW %d %d" % (i, j))
                    self.nValidations.append((j, witness, nCommit))

        toc = cnt()
        print(f"Validation done in {(toc - tic) / self.PARTIES:0.6f} seconds per party i")
        return oldCommittee, newCommittee

    def accusation(self):
        """
        Protocol 4 "Accusation-Response"
        """
        # Check if one of the validation lists contains an entry, which indicates an accusation is made
        # If it is empty then all parties are honest
        # If there is one print the accusation
        # The party will publish the shares with the witness
        # Compute the validation once again
        # If the validation fails then the party is corrupt
        # If the validation is ok then the party is honest
        print("PROTOCOL 4 ACCUSATION")
        if len(self.oValidations) > 0 or len(self.nValidations) > 0:
            try:
                for party in self.oValidations:
                    print("accuse,", party[0])
                    print("Publishing witness: ", party)
                    i = party[0]
                    xi, witnessTup = list(party[1])[0]
                    w, fx, hx = witnessTup
                    if not check_proof_single(party[2], w, xi, fx, hx, self.__setup):
                        print("Party %d is corrupted" % i)
                    else:
                        print("Party %d is honest " % i)
            except IndexError:
                pass
        else:
            print("All parties are honest :-)")

    def verification(self, oldC, newC):
        """
        Protocol 5 "Verification"
        """

        # committee = {1 : [u,v,w,uShares,vShares]}
        # committee = {1 : [mu,vu,w,muShares,vuShares]}
        print("PROTOCOL 5 VERIFICATION")

        def _verificationPoly(X, firstShares, secondShares):
            """
            Compute the shares of the polynomials F(X) = (mu + u*X)*X^(2i-2), H(X) = (vu + v*X)*X^(2*i-2)
            :param X: a scalar which was generated from the Challenge protocol i.e. the lambdas
            :param i: The i-th party
            :param firstShares: the mu shares
            :param secondShares: the u shares
            :return: shares, the coeff of the polynomial
            """
            s = 0
            coeff = [0] * (len(firstShares) + len(secondShares))
            for i in range(self.PARTIES):
                if i % 2 == 0:
                    # print(firstShares[i][1])
                    coeff[i] = firstShares[i][1]
                if i % 2 == 1:
                    coeff[i] = secondShares[i][1]

                s = (firstShares[i][1] + secondShares[i][1] * X) * X ** (2 * i - 2)
            return s, coeff

        def _compute(committeeD1, committeeD2, i, lambdas):
            """
            Provide the shares for the computation of the verification polynomials
            :param committeeD1: The coupled sharing from the first distribution invocation
            :param committeeD2: The coupled sharing from the second distribution invocation
            :param i: the i-th party
            :param lambdas: the scalars generated from the Challenge protocol
            :return: shares
            """
            mu = committeeD2[i][0]
            u = committeeD1[i][0]
            vu = committeeD2[i][1]
            v = committeeD1[i][1]
            fx = _verificationPoly(lambdas[i], mu, u)
            hx = _verificationPoly(lambdas[i], vu, v)
            return fx, hx

        def _reconstruction(shares, committee):
            """
            Reconstruction of the F(X) and H(X)
            :param shares: list where the shares will be stored
            :param committee: the shares of the parties
            :return: list of shares
            """
            for i in range(1, self.THRESHOLD + 2):
                shares[i] = (i, committee[i][0])

            return self.sss.reconstruct(shares)

        def _commitments(firstPoly, secondPoly, party):
            u = self.sss.getPoly(firstPoly[party][0])
            v = self.sss.getPoly(firstPoly[party][1])
            mu = self.sss.getPoly(secondPoly[party][0])
            vu = self.sss.getPoly(secondPoly[party][1])
            assert len(u) + len(v) + len(mu) + len(vu) == 4 * self.THRESHOLD
            return commit_to_poly(u, v, self.__setup), commit_to_poly(mu, vu, self.__setup)

        # Invoke the distribution protocol to create the mu and vu coupled sharing
        print("EXECUTE PROTOCOL 3 SECOND TIME")
        oldCommitteeD2, newCommitteeD2 = self.distribution()
        print("EXECUTE CHALLENGE PROTOCOL")
        lambdas = challenge(self.PARTIES)
        oldCommittee = {}
        newCommittee = {}
        # TODO: MAKE HASH
        x = 5431

        tic = cnt()
        print("COMPUTING F(X), H(X), F~(X), H~(X) AND THEIR WITNESSES")
        for i in range(self.PARTIES):
            # Create the F(X) and H(X) polynomials
            # Compute the witnesses for those polynomials
            # For the new/old committee create the dictionary {party : (F(X),H(X),w}
            fx, hx = _compute(oldC, oldCommitteeD2, i, lambdas)
            oldCommittee[i] = (fx[0], hx[0],
                               compute_proof_single(fx[1], hx[1], x, self.__setup))
            fx, hx = _compute(newC, newCommitteeD2, i, lambdas)
            newCommittee[i] = (fx[0], hx[0],
                               compute_proof_single(fx[1], hx[1], x, self.__setup))
        toc = cnt()
        print(f"Compute F(X) and H(X) with their w in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        oCommit = {}
        nCommit = {}
        tic = cnt()
        # TODO: MAKE TO COMMITMENT VERIFICATION
        # for i in range(self.PARTIES):
        #     # Compute the commitments for the F(X) and H(X)
        #
        #     oCommit[i] = _commitments(oldC,oldCommitteeD2,i)
        #
        #     nCommit[i] = _commitments(newC,newCommitteeD2,i)
        toc = cnt()
        print("STILL NOT VALIDATING THE COMMITMENT - TODO")
        # print(f"STILL NOT DONE!!!!Compute commitments {toc - tic:0.6f} seconds")

        tic = cnt()
        print("START RECONSTCTION OF F(X) H(X) F~(X) H~(X) FROM T+1 SHARES")
        shares = [(0, 0)] * (self.THRESHOLD + 2)
        f = _reconstruction(shares, oldCommittee)
        fTilde = _reconstruction(shares, newCommittee)
        h = _reconstruction(shares, oldCommittee)
        hTilde = _reconstruction(shares, newCommittee)
        assert f == fTilde
        assert h == hTilde
        toc = cnt()
        print(f"Equalities are ok {toc - tic:0.6f} seconds")

        checkOldCommitments = {}
        checkNewCommitments = {}
        # for i in range(self.PARTIES):
        #     # Compute the commitments for the F(X) and H(X)
        #
        #     checkOldCommitments[i] = _commitments(oldC, oldCommitteeD2, i)
        #
        #     checkNewCommitments[i] = _commitments(newC, newCommitteeD2, i)
        #
        # assert checkNewCommitments == nCommit
        # assert checkOldCommitments == oCommit

    def output(self, oldCommittee, newCommittee):
        """
        Protocol 7 "Output"
        :return:
        """
        print("STARTING PROTOCOL 7 OUTPUT")
        # make a n x n-t Vandermonde matrix
        vander = vanderMatrix(self.PARTIES, self.THRESHOLD)
        r = {}
        phy = {}
        rTilde = {}
        phyTilde = {}
        tic = cnt()
        for i in range(self.PARTIES):
            # compute the vector ([r1]...[r_n-t])
            r[i] = computeVanderElem(vander, oldCommittee[i][0])
            # compute the vector ([phy1]...[phy_n-t])
            phy[i] = computeVanderElem(vander, oldCommittee[i][1])
            rTilde[i] = computeVanderElem(vander, newCommittee[i][0])
            phyTilde[i] = computeVanderElem(vander, newCommittee[i][1])

        toc = cnt()
        print(
            f"COMPUTED VANDERMONDE ELEMENTS [r] [phy] [r~] [phy~] in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        oCommit = {}
        oProof = {}
        # x = {}
        print("COMMITING TO R AND PHY AND THEIR WITNESSES FOR THE OLD COMMITTEE")
        x = [i for i in range(100, 110)]
        tic = cnt()
        for i in range(self.PARTIES):
            uSharesOldCommittee = oldCommittee[i][0]
            vSharesOldCommittee = oldCommittee[i][1]
            commitments = []
            witnesses = []
            for j in range(self.PARTIES):
                ui = [uSharesOldCommittee[j][1]] * self.THRESHOLD
                vi = [vSharesOldCommittee[j][1]] * self.THRESHOLD
                commit = commit_to_poly(ui, vi, self.__setup)
                # hashing = fsh(self.__setup, commit)
                # x = int.from_bytes(hashing.read(j + 1), byteorder='big')
                polyEvals = self.__eval(ui, vi, x[j])
                witness = compute_proof_single(ui, vi, x[j], self.__setup)
                commitments.append(commit)
                witnesses.append((witness, polyEvals[0], polyEvals[1], x[j]))
                break

            oCommit[i] = commitments
            oProof[i] = witnesses

        toc = cnt()
        print(f"OLD COMMITTEE DONE in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        nCommit = {}
        nProof = {}
        print("COMMITING TO R AND PHY AND THEIR WITNESSES FOR THE NEW COMMITTEE")
        tic = cnt()

        for i in range(self.PARTIES):
            uSharesNewCommittee = newCommittee[i][0]
            vSharesNewCommittee = newCommittee[i][1]
            commitments = []
            witnesses = []
            for j in range(self.PARTIES):
                ui = [uSharesNewCommittee[j][1]] * self.THRESHOLD
                vi = [vSharesNewCommittee[j][1]] * self.THRESHOLD
                commit = commit_to_poly(ui, vi, self.__setup)
                # hashing = fsh(self.__setup, commit)
                # x = int.from_bytes(hashing.read(j + 1), byteorder='big')
                polyEvals = self.__eval(ui, vi, x[j])
                witness = compute_proof_single(ui, vi, x[j], self.__setup)
                commitments.append(commit)
                witnesses.append((witness, polyEvals[0], polyEvals[1], x[j]))
                break

            nCommit[i] = commitments
            nProof[i] = witnesses

        toc = cnt()
        print(f"NEW COMMITTEE DONE in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        return r, phy, rTilde, phyTilde, oCommit, nCommit, oProof, nProof

    def refresh(self, r, phy, s, z, rTilde, phyTilde, szWitnesses, szCommitments, rphyWitnesses, rphyCommitments):
        """
        Protocol 8 "Refresh"
        :param oldCommittee:
        :param newCommittee:
        :return:
        """
        # Compute [s+r] = [s] + [r]
        # Compute [z+phy] = [z] + [phy]
        # {Party : [u],[v],w,[s],[r],[z],[phy]}
        # {Party: (sr,zphy)}
        print("PROTOCOL 8 REFRESH")
        print("NOTE: I DONT HAVE COMMITMENTS AND WITNESSES HERE SO NO VALIDATIONS")
        sr = {}
        zphy = {}
        kingSR = []
        kingZPHY = []
        print("COMPUTING S+R AND Z+PHY. ALSO SENDING THEM TO P-KING")
        tic = cnt()

        for i in range(1, self.PARTIES + 1):
            sr[i] = s[i] + r[i - 1][0]
            zphy[i] = z[i] + phy[i - 1][0]
            kingSR.append((i, s[i] + r[i - 1][0]))
            kingZPHY.append((i, z[i] + phy[i - 1][0]))
        toc = cnt()
        print(f"COMPUTATION DONE in {(toc - tic) / self.PARTIES:0.6f} seconds per party")
        oProofs = {}
        oCommit = {}
        for i in range(self.PARTIES):
            szWitness, xi, p1, p2 = szWitnesses[i]
            rphyWitness, p3, p4, xj = rphyWitnesses[i][0]
            oProofs[i] = [curve.add(szWitness, rphyWitness), p1 + p3, p2 + p4, xj]

            szCommit = szCommitments[i]
            rphyCommit = rphyCommitments[i][0]
            oCommit[i] = curve.add(szCommit, rphyCommit)

        # The parties give the witness to the king
        # the king knows the commitments cus they are published
        for i in range(self.THRESHOLD + 1):
            w, fx, hx, x = oProofs[i]

            if not check_proof_single(oCommit[i], w, x, fx, hx, self.__setup):
                print("BAD VALIDATION FOR KING :((")
            else:
                print("OK VALIDATION FOR KING")

        print("RECONSTRUCT S+R AND Z+PHY")
        srReconstruct = self.sss.getPoly(kingSR)
        zphyReconstruct = self.sss.getPoly(kingZPHY)

        commitment = commit_to_poly(srReconstruct, zphyReconstruct, self.__setup)
        polyEvals = self.__eval(srReconstruct, zphyReconstruct, 100)
        proof = compute_proof_single(srReconstruct, zphyReconstruct, 100, self.__setup)
        wintess = [proof, polyEvals[0], polyEvals[1], 100]

        nCommit = {}
        nProofs = {}
        for i in range(self.PARTIES):
            r_phyWitness, rEval, phyEval, b = rphyWitnesses[i][0]
            nProofs[i] = [curve.add(wintess[0], curve.neg(r_phyWitness)), wintess[1] - rEval,
                          wintess[2] - phyEval, 100]
            r_phyCommitment = rphyCommitments[i][0]
            nCommit[i] = curve.add(commitment, curve.neg(r_phyCommitment))

        s = {}
        z = {}

        print("COMPUTE S+R-R~ AND Z+PHY-PHY~")
        for i in range(1, self.PARTIES + 1):
            s[i] = srReconstruct[0] - rTilde[i - 1][0]
            z[i] = zphyReconstruct[0] - phyTilde[i - 1][0]

        return s, z, nCommit, nProofs

    def reconstruction(self, shares, coomimtnets, proofs):
        print("RECONSTRUCT SECRET")
        for i in range(self.PARTIES):
            w, fx, hx, x = proofs[i]
            c = coomimtnets[i]
            if not check_proof_single(c, w, x, fx, hx, self.__setup):
                print("BAD VALIDATION FOR CLIENT")
            else:
                print("GOOD VALIDATION FOR CLIENT")
        return self.sss.reconstruct(shares)
