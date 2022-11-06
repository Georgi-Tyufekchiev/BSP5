from functools import reduce
from time import perf_counter as cnt

import numpy as np
from Crypto.Random import get_random_bytes as rng
from Crypto.Util.number import bytes_to_long
from numpy.polynomial import Polynomial
from numpy.polynomial.polynomial import polyval


def randNum():
    return bytes_to_long(rng(8))


# noinspection PyShadowingNames
class SSS:

    def __init__(self, n, k):
        """
        Initialize Shamir Secret Sharing Scheme
        :param n: number of shares
        :param k: threshold to reconstruct the secret
        """
        if k > n:
            raise ValueError("Number of shares must be greater than the threshold")
        self.__n = n
        self.__k = k
        self.__p = 2 ** 521 - 1  # Mersenne prime

    def __polynomial(self, s):
        """
        Create a Shamir polynomial of degree k-1
        :param s: secret used as free coeff
        :return: Polynomial coeff in increasing degree
        """
        coefficients = [s] + [bytes_to_long(rng(16)) for _ in range(1, self.__k)]
        self._shamirPoly = Polynomial(coefficients)

        return self._shamirPoly.coef

    def splitSecret(self, s, polyCoeff=None):
        """
        Split the secret into shares
        :param s: secret
        :param polyCoeff: polynomial coefficients in rising order. Default is None
        :return: a list of shares
        """
        if polyCoeff is None:
            _f = self.__polynomial(s)
        else:
            _f = Polynomial(polyCoeff).coef
        shares = [(x, polyval(x, _f) % self.__p) for x in range(1, self.__n + 1)]
        return shares

    def reconstruct(self, shares):
        """
        Reconstruct the secret provided the minimum number of shares
        :param shares: a list of shares
        :return: secret
        """
        if len(shares) < self.__k:
            raise ValueError("Provided shares are not enough to reconstruct")
        x = [a for a, b in shares]
        y = [b for a, b in shares]
        return self.__interpolate(x, y)

    def coupledSharing(self):
        """
        Create coupled sharing
        :return: shares and the polynomial associated with them
        """
        u = randNum()
        # Create polynomial for u and u~
        uPoly = (self.__polynomial(u), self.__polynomial(u))
        # Create shares for u and u~
        uShares = (self.splitSecret(u, uPoly[0]), self.splitSecret(u, uPoly[1]))

        v = randNum()
        # Create polynomial for v and v~
        vPoly = (self.__polynomial(v), self.__polynomial(v))
        # Create shares for v and v~
        vShares = (self.splitSecret(v, uPoly[0]), self.splitSecret(v, uPoly[1]))
        return uPoly, vPoly, uShares, vShares

    def sampleSharing(self):
        elem = randNum()
        poly = self.__polynomial(elem)
        shares = self.splitSecret(elem, poly)
        return shares, poly

    def __interpolate(self, x, y):
        """
        Lagrange's interpolation to recover secret
        :param x: points on the x-axis
        :param y: points on the y-axis
        :return: secret
        """

        def _basis(j, k):
            l = [x[m] * pow(x[m] - x[j], -1, self.__p) for m in range(k) if m != j]
            return reduce(lambda a, b: (a * b) % self.__p, l)

        assert len(x) != 0 and (len(x) == len(y))

        k = len(x)
        f = [y[j] * _basis(j, k) for j in range(k)]

        return sum(f) % self.__p
    # def test(self,shares):
    #     M = len(x)
    #     p = np.poly1d(0)
    #     for j in range(M):
    #         pt = np.polynomial.Polynomial(y[j])
    #         for k in range(M):
    #             if k == j:
    #                 continue
    #             fac = pow(x[j] - x[k], -1, self.__p)
    #             pt *= np.polynomial.Polynomial([(-x[k]) * fac % self.__p, fac])
    #             for coeff in range(len(pt.coef)):
    #                 pt.coef[coeff] %= self.__p
    #
    #         p += pt
    #         if j != 0:
    #             for coeff in range(len(p.coef)):
    #                 p.coef[coeff] %= self.__p
    def getPoly(self, shares):

        shares = list(shares)
        x = [shares[i][0] for i in range(self.__k)]
        y = [shares[i][1] for i in range(self.__k)]
        # print(x)
        # print(y)

        def _polyAdd(poly1, poly2):
            coeff1 = poly1
            coeff2 = poly2
            res = [0] * (len(coeff1))
            for i in range(len(coeff1)):
                res[i] += (coeff1[i] + coeff2[i]) % self.__p
            return res

        def _polyMul(poly1, poly2):
            coeff1 = poly1
            coeff2 = poly2
            res = [0] * (len(coeff1) + len(coeff2) - 1)
            for position1, a in enumerate(coeff1):
                for position2, b in enumerate(coeff2):
                    res[position1 + position2] += (a * b) % self.__p
            return res

        def _basis(j, k):
            l = []
            for m in range(k):
                if m == j:
                    continue
                fac = pow(x[j] - x[m], -1, self.__p)
                l.append([(-x[m] * fac) % self.__p, fac])

            p = _polyMul(l[0], l[1])
            for poly in l[2:]:
                p = _polyMul(p, poly)
            return p

        tic = cnt()

        k = len(x)
        f = []
        for j in range(k):
            poly = _basis(j, k)
            tmp = []
            for coeff in poly:
                tmp.append((y[j] * coeff) % self.__p)
            f.append(tmp)

        res = _polyAdd(f[0], f[1])
        for poly in f[2:]:
            res = _polyAdd(poly, res)
        toc = cnt()
        # print(f"Poly {toc - tic:0.10f} seconds")

        return res


if __name__ == "__main__":
    # Assume 10 parties with t = 4
    parties = 10
    t = 4
    # ui = [randNum() for i in range(parties)]
    sss = SSS(parties, t)
    s = 100
    shares = sss.splitSecret(s)
    x = [shares[i][0] for i in range(8)]
    y = [shares[i][1] for i in range(8)]
    p = sss.test(shares)

    print(p)
    # poly = sss.getPoly(x, y)
    # uiShares = [sss.splitSecret(u) for u in ui]
    # ui_iShare = [uiShares[i][i][1] for i in range(parties)]
    # vander = vanderMatrix(parties, t)
    # ri = computeRandElem(vander, ui_iShare)
    # print(ri)
    # x = 2 ** 512 - 1
    # print(math.log(x, 2))
    # print(math.log(x, 2) / parties / 8)
    # print(rng(3))


