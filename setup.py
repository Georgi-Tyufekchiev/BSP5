from time import perf_counter as cnt

from KZG import *
from SSS import *
from utils import *
from hand_off import *


class Setup:
    validations = []

    def __init__(self):
        """
        Initialise the (n,k) Shamir secret sharing scheme along with the Trusted Setup, which will create the PK
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
        committee = {}
        commit = {}
        print("PROTOCOL DISTRIBUTION:")
        tic = cnt()

        for i in range(self.PARTIES):
            committee[i] = [self.sss.sampleSharing(), self.sss.sampleSharing(), [], [], []]
            poly1 = committee[i][0][1]
            poly2 = committee[i][1][1]
            commit[i] = commit_to_poly(poly1, poly2, self.__setup)
        toc = cnt()
        print(f"SHARING + COMMITMENT done in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        proof = {}
        x = [i for i in range(100, 110)]
        tic = cnt()

        for i in range(self.PARTIES):
            uPoly = committee[i][0]
            vPoly = committee[i][1]
            for j in range(self.PARTIES):
                polyEvals = self.__eval(uPoly[1], vPoly[1], x[j])
                proof[i] = [compute_proof_single(uPoly[1], vPoly[1], x[j], self.__setup), polyEvals[0], polyEvals[1],
                            x[j]]
        toc = cnt()
        print(f"PROOFS DONE IN {(toc - tic) / self.PARTIES:0.6f} seconds per party")
        print("DISTRIBUTING SHARES AND WITNESSES")
        tic = cnt()

        for i in range(self.PARTIES):
            uShares = committee[i][0][0]
            vShares = committee[i][1][0]

            # for each witness extract the following: [x,(proof,f(x),h(x))]
            witness = proof[i]
            for j in range(self.PARTIES):
                committee[j][2].append(uShares[j])
                committee[j][3].append(vShares[j])
                committee[j][-1].append(witness)
        toc = cnt()
        print(f"DONE IN {(toc - tic) / self.PARTIES:0.6f} seconds per party i")
        print("VALIDATING SHARES")
        tic = cnt()

        for i in range(self.PARTIES):
            for j in range(self.PARTIES):
                witness = committee[i][-1][j]
                w, fx, hx, xi = witness
                oCommit = commit[j]

                if not check_proof_single(oCommit, w, xi, fx, hx, self.__setup):
                    print("Validation BAD FOR OLD %d %d" % (i, j))
                    self.validations.append((j, witness, oCommit))
        toc = cnt()
        print(f"VALIDATION IN {(toc - tic) / self.PARTIES:0.6f} seconds per party i")

        # { Party : u,v,shares1,shares2,w}
        return committee

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
        print("PROTOCOL ACCUSATION")
        if len(self.validations) > 0:
            try:
                for party in self.validations:
                    print("accuse,", party[0])
                    print("Publishing witness: ", party)
                    i = party[0]
                    w, fx, hx, xi = party[1]
                    if not check_proof_single(party[2], w, xi, fx, hx, self.__setup):
                        print("Party %d is corrupted" % i)
                    else:
                        print("Party %d is honest " % i)
            except IndexError:
                pass
        else:
            print("All parties are honest :-)")

    def verification(self, committee):
        """
        Protocol 5 "Verification"
        """
        print("PROTOCOL VERIFCATION")

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
            for i in range(1, self.PARTIES):
                if (i - 1) % 2 == 0:
                    # print(firstShares[i][1])
                    coeff[i] = firstShares[i - 1][1]
                if (i - 1) % 2 == 1:
                    coeff[i] = secondShares[i - 1][1]

                s = (firstShares[i - 1][1] + secondShares[i - 1][1] * X) * X ** (2 * i - 2)
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
            mu = committeeD2[i][2]
            u = committeeD1[i][2]
            vu = committeeD2[i][3]
            v = committeeD1[i][3]
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
        # { Party : u,v,shares1,shares2,w}
        print("EXECUTE SECOND DISTRIBUTION")
        committeeD2 = self.distribution()
        print("EXECUTE CHALLENGE")
        lambdas = challenge(self.PARTIES)
        newCommittee = {}
        #  TODO: MAKE HASH
        x = 5431

        tic = cnt()
        print("COMPUTE F(X) AND H(X)")
        for i in range(self.PARTIES):
            # Create the F(X) and H(X) polynomials
            # Compute the witnesses for those polynomials
            # For the new/old committee create the dictionary {party : (F(X),H(X),w}
            fx, hx = _compute(committee, committeeD2, i, lambdas)
            newCommittee[i] = (fx[0], hx[0],
                               compute_proof_single(fx[1], hx[1], x, self.__setup))

        toc = cnt()
        print(f"Compute F(X) and H(X) with their w in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        oCommit = {}
        tic = cnt()
        # TODO: MAKE TO COMMITMENT VERIFICATION
        # for i in range(self.PARTIES):
        #     # Compute the commitments for the F(X) and H(X)
        #
        #     oCommit[i] = _commitments(oldC,oldCommitteeD2,i)
        #
        toc = cnt()
        print("STILL NOT VALIDATING THE COMMITMENT - TODO")

        tic = cnt()
        print("START RECONSTCTION OF F(X) H(X)  FROM T+1 SHARES")

        shares = [(0, 0)] * (self.THRESHOLD + 2)
        f = _reconstruction(shares, newCommittee)
        h = _reconstruction(shares, newCommittee)
        toc = cnt()

        checkOldCommitments = {}
        # for i in range(self.PARTIES):
        #     # Compute the commitments for the F(X) and H(X)
        #
        #     checkOldCommitments[i] = _commitments(oldC, oldCommitteeD2, i)
        #
        #
        # assert checkOldCommitments == oCommit

    def output(self, committee):
        """
        Protocol 7 "Output"
        :return:
        """
        print("STARTING PROTOCOL OUTPUT")

        vander = vanderMatrix(self.PARTIES, self.THRESHOLD)
        r = {}
        phy = {}
        tic = cnt()

        for i in range(self.PARTIES):
            r[i] = computeVanderElem(vander, committee[i][2])
            phy[i] = computeVanderElem(vander, committee[i][3])
        toc = cnt()
        print(f"COMPUTED VANDERMONDE ELEMENTS [r] [phy] in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        commit = {}
        proof = {}
        print("COMMITING TO R AND PHY AND THEIR WITNESSES")
        tic = cnt()

        x = [i for i in range(100, 110)]
        for i in range(self.PARTIES):
            shares1 = r[i]
            shares2 = phy[i]
            poly1 = self.sss.getPoly(enumerate(shares1, start=1))
            poly2 = self.sss.getPoly(enumerate(shares2, start=1))
            commit[i] = commit_to_poly(poly1, poly2, self.__setup)
            polyEvals = self.__eval(poly1, poly2, x[i])
            proof[i] = [compute_proof_single(poly1, poly2, x[i], self.__setup), polyEvals[0], polyEvals[1],
                        x[i]]
        toc = cnt()
        print(f"OLD COMMITTEE DONE in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        return r, phy, commit, proof

    def refresh(self, r, phy, commitments, proof):
        """
        Protocol 8 "Refresh"
        :param oldCommittee:
        :param newCommittee:
        :return:
        """
        print("PROTCOL FRESH SETUP")
        tic = cnt()

        def _client():
            print("CLIENT RECEIVES SHARES AND VALIDATES T+1 OF THEM")
            for j in range(self.THRESHOLD + 1):
                w, fx, hx, xi = proof[j]

                if not check_proof_single(commitments[j], w, xi, fx, hx, self.__setup):
                    print("Validation BAD FOR OLD %d" % (j))
                    self.validations.append((j, proof[j], commitments[j]))

            rShares = [r[i][0] for i in range(len(r))]
            phyShares = [phy[i][0] for i in range(len(phy))]
            print("CLIENT RECONSTRUCTS R AND PHY")
            rReconstruct = self.sss.reconstruct(list(enumerate(rShares, start=1)))
            phyReconstruct = self.sss.reconstruct(list(enumerate(phyShares, start=1)))
            z = randNum()
            secret = 10
            print("COMPUTE S+R AND Z+PHY")
            sr = secret + rReconstruct
            zphy = z + phyReconstruct
            return sr, zphy, rReconstruct

        sr, zphy, rRec = _client()
        sShares = {}
        zShares = {}
        print("EACH PARTY COMPUTES S+R-R AND Z+PHY-PHY")
        for i in range(1, self.PARTIES + 1):
            sShares[i] = sr - r[i - 1][0]
            zShares[i] = zphy - phy[i - 1][0]
        toc = cnt()
        print(f"FINISH PROTOCOL in {(toc - tic):0.6f} seconds")

        return sShares, zShares, rRec

    def r(self, shares):
        s = self.sss.reconstruct(shares)
        return s


if __name__ == "__main__":
    print("THE SECRET IS THE NUMBER 10")
    print()
    test = Setup()
    print()
    c = test.distribution()
    print()
    test.accusation()
    print()
    test.verification(c)
    print()
    r, phy, commit, proof = test.output(c)
    print()
    s1, z1, rRec = test.refresh(r, phy, commit, proof)
    print()
    # res = list(s1.items())
    # print(test.r(res))

    final = Handoff()
    print()
    o, c = final.distribution()
    print()

    final.accusation()
    print()

    final.verification(o, c)
    print()

    r, phy, rTilde, phyTilde, oCommit, nCommit, oProof, nProof = final.output(o, c)
    print()

    s, z = final.refresh(r, phy, s1, z1, rTilde, phyTilde)
    print()

    res = list(s.items())
    print(final.r(res))
