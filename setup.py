from operator import add
from py_ecc import optimized_bls12_381 as curve

from SSS import *
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
        """
        Evaluate polynomials at point x
        :param f: a list of poly coeff
        :param h: a list of poly coeff
        :param x: point to evaluate at
        :return: evaluation of f and h
        """
        fx = eval_poly_at(f, x)
        hx = eval_poly_at(h, x)
        return fx, hx

    def distribution(self):
        """
        Protocol 10 "Setup-Dist"
        :return:
        """
        # a dict to store the sample sharings for each party
        # also contains lists for the future distribution of shares
        # the last list for witnesses
        committee = {}
        commit = {}
        print("PROTOCOL DISTRIBUTION:")
        tic = cnt()

        for i in range(self.PARTIES):
            # Each sample sharing function will give a list of shares and the polynomial
            committee[i] = [self.sss.sampleSharing(), self.sss.sampleSharing(), [], [], []]
            poly1 = committee[i][0][1]
            poly2 = committee[i][1][1]
            # compute the commitment to u and v for each party
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
                # evaluate the polynomials of u and v at point x
                polyEvals = self.__eval(uPoly[1], vPoly[1], x[j])
                # compute the witness which is the tuple (proof, f(x), h(x), x)
                # the witness has to be prepared by each party for each party
                proof[i] = [compute_proof_single(uPoly[1], vPoly[1], x[j], self.__setup), polyEvals[0], polyEvals[1],
                            x[j]]
        toc = cnt()
        print(f"PROOFS DONE IN {(toc - tic) / self.PARTIES:0.6f} seconds per party")
        print("DISTRIBUTING SHARES AND WITNESSES")
        tic = cnt()

        # Each party i will send their j-th share to the j-th party
        # the j-th witness will be sent to the j-th party
        for i in range(self.PARTIES):
            uShares = committee[i][0][0]
            vShares = committee[i][1][0]

            # for each witness extract the following: [x,(proof,f(x),h(x))]
            witness = proof[i]
            for j in range(self.PARTIES):
                committee[j][2].append(uShares[j])
                committee[j][3].append(vShares[j])
                # the witness is always the last element for each party
                committee[j][-1].append(witness)
        toc = cnt()
        print(f"DONE IN {(toc - tic) / self.PARTIES:0.6f} seconds per party i")
        print("VALIDATING SHARES")
        tic = cnt()

        # each party i will take the j-th witness and the j-th commit
        # each party i will check the validity of the shares with those values
        # if the validation is bad the party will prepare and accusation
        # the accusation is the tuple (j-th party, witness, commitment
        # for i in range(self.PARTIES):
        #     for j in range(self.PARTIES):
        #         witness = committee[i][-1][j]
        #         w, fx, hx, xi = witness
        #         oCommit = commit[j]
        #
        #         if not check_proof_single(oCommit, w, xi, fx, hx, self.__setup):
        #             print("Validation BAD FOR OLD %d %d" % (i, j))
        #             self.validations.append((j, witness, oCommit))
        # toc = cnt()
        # print(f"VALIDATION IN {(toc - tic) / self.PARTIES:0.6f} seconds per party i")

        # { Party : u,v,shares1,shares2,w}
        return committee

    def accusation(self):
        """
        Protocol 11 "Accusation-Response"
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
        Protocol 12 "Verification"
        """
        print("PROTOCOL VERIFCATION")

        def _verificationPoly(X, firstShares, secondShares):
            """
            Compute the shares of the polynomials F(X) = (mu + u*X)*X^(2i-2), H(X) = (vu + v*X)*X^(2*i-2)
            :param X: a scalar which was generated from the Challenge protocol i.e. the lambdas
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
            :param committeeD1: The sampled sharings from the first distribution invocation
            :param committeeD2: The sampled sharings from the second distribution invocation
            :param i: the i-th party
            :param lambdas: the scalars generated from the Challenge protocol
            :return: shares, list of coeff
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
            :return: a reconstruction of either polynomial
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
        print("EXECUTE SECOND DISTRIBUTION")
        committeeD2 = self.distribution()
        print("EXECUTE CHALLENGE")
        # the challenge protocol will produce the lambdas
        lambdas = challenge(self.PARTIES)
        newCommittee = {}
        #  TODO: MAKE HASH
        x = 5431

        tic = cnt()
        print("COMPUTE F(X) AND H(X)")
        for i in range(self.PARTIES):
            # Create the shares for F(X) and H(X)
            fx, hx = _compute(committee, committeeD2, i, lambdas)
            newCommittee[i] = (fx[0], hx[0])


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
        Protocol 14 "Output"
        :return:
        """
        print("STARTING PROTOCOL OUTPUT")

        # make a n x n-t Vandermonde matrix
        vander = vanderMatrix(self.PARTIES, self.THRESHOLD)
        r = {}
        phy = {}
        tic = cnt()

        for i in range(self.PARTIES):
            # compute the vector ([r1]...[r_n-t])
            r[i] = computeVanderElem(vander, committee[i][2])
            # compute the vector ([phy1]...[phy_n-t])
            phy[i] = computeVanderElem(vander, committee[i][3])
        toc = cnt()
        print(f"COMPUTED VANDERMONDE ELEMENTS [r] [phy] in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        commit = {}
        proof = {}
        print("COMMITING TO R AND PHY AND THEIR WITNESSES")
        x = [i for i in range(1, 11)]
        tic = cnt()

        for i in range(self.PARTIES):
            uShares = committee[i][2]
            vShares = committee[i][3]
            commitments = []
            witnesses = []
            for j in range(self.PARTIES):
                # Compute the commitment of each r and phy for each party
                # Compute the witness for each r and phy for each party
                ui = [uShares[j][1]] * self.THRESHOLD
                vi = [vShares[j][1]] * self.THRESHOLD
                commitment = commit_to_poly(ui, vi, self.__setup)
                polyEvals = self.__eval(ui, vi, x[j])
                witness = compute_proof_single(ui, vi, x[j], self.__setup)
                commitments.append(commitment)
                witnesses.append((witness, polyEvals[0], polyEvals[1], x[j]))

            commit[i] = commitments
            proof[i] = witnesses

        toc = cnt()
        print(f" COMMITTEE DONE in {(toc - tic) / self.PARTIES:0.6f} seconds per party")

        return r, phy, commit, proof

    def refresh(self, r, phy, commitments, proof):
        """
        Protocol 15 "Fresh"
        :param r: vector of r shares
        :param phy: vector of phy shares
        :param commitments: dictionary which has all the commitments for each party
        :param proof: dictionary which has all the witnesses for each party
        :return:
        """
        print("PROTCOL FRESH SETUP")
        tic = cnt()

        def _client():
            """
            This function simulates the operations of the client
            :return: s+r, z+phy, reconstruction of r
            """
            print("CLIENT RECEIVES SHARES AND VALIDATES T+1 OF THEM")
            # the client will receive n shares of r
            # they will take the first t+1 shares that pass the validation
            # for now we assume the parties are honest, so we know the first t+1 are already valid
            for j in range(self.THRESHOLD + 1):
                w, fx, hx, xi = proof[j][0]

                if not check_proof_single(commitments[j][0], w, xi, fx, hx, self.__setup):
                    print("Validation BAD FOR OLD %d" % (j))
                    self.validations.append((j, proof[j][0], commitments[j][0]))

            # take out the sharing value for r from the tuple (x,y)
            rShares = [r[i][0] for i in range(len(r))]
            # take out the sharing value for phy from the tuple (x,y)
            phyShares = [phy[i][0] for i in range(len(phy))]
            print("CLIENT RECONSTRUCTS R AND PHY")
            # Reconstruct the ull polynomials or r and phy
            rReconstruct = self.sss.getPoly(list(enumerate(rShares, start=1)))
            phyReconstruct = self.sss.getPoly(list(enumerate(phyShares, start=1)))
            # sample a random r and its polynomial
            z = [randNum()] + [bytes_to_long(rng(8)) for _ in range(1, self.THRESHOLD)]
            # take a random secret value e.g and make a polynomial out of it
            secret = [10] + [bytes_to_long(rng(8)) for _ in range(1, self.THRESHOLD)]
            print("COMPUTE S+R AND Z+PHY")
            # add the polynomials s+r
            sr = list(map(add, rReconstruct, secret))
            # add the polynomials z+phy
            zphy = list(map(add, phyReconstruct, z))
            return sr, zphy, rReconstruct

        sr, zphy, rRec = _client()

        # since s+r is public, the same commitment will be used for all parties
        commitment = commit_to_poly(sr, zphy, self.__setup)
        x = [i for i in range(100, 110)]

        partyCommitments = {}
        proofs = {}

        # all parties compute the proof for their s+r
        # each party will take the witness for the [r] and [phy] from the protocol 14
        # each party will take the commitment for the [r] and [phy] from protocol 14
        # The witness is the ratio w(s+r,z+phy)/w([r],[phy]) = w1 * w2^(-1) = w1 + neg(w2)
        # The same is the done for the commitments
        # we do this because the witness and the commitment is an elliptic curve point (x,y,z)
        for i in range(self.PARTIES):
            publicSharingWitness = compute_proof_single(sr, zphy, x[i], self.__setup)
            r_phyWitness = proof[i][0][0]
            proofs[i] = curve.add(publicSharingWitness, curve.neg(r_phyWitness))
            r_phyCommitment = commitments[i][0]
            partyCommitments[i] = curve.add(commitment, curve.neg(r_phyCommitment))

        sShares = {}
        zShares = {}
        print("EACH PARTY COMPUTES S+R-R AND Z+PHY-PHY")
        # each party will compute s+r - [r]
        # each party will compute z+phy - [phy]
        for i in range(1, self.PARTIES + 1):
            sShares[i] = sr[0] - r[i - 1][0]
            zShares[i] = zphy[0] - phy[i - 1][0]
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
