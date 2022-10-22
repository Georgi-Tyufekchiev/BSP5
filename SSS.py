import math
from functools import reduce

import numpy as np
from Crypto.Random import get_random_bytes as rng
from Crypto.Util.number import bytes_to_long


def randNum():
    return bytes_to_long(rng(8))


class SSS:

    def __init__(self, n, k):
        """
        Initialize Shamir Secret Sharing Scheme
        :param n: number of shares
        :param k: threshold to reconstruct the secret
        """
        if k > n:
            raise Exception("Number of shares must be greater than the threshold")
        self.__n = n
        self.__k = k
        self.__p = 2 ** 521 - 1  # Mersenne prime

    def __polynomial(self, s):
        """
        Create a Shamir polynomial of degree k-1
        :param s: secret used as free coeff
        :return: Polynomial coeff in increasing degree
        """
        coefficients = [s] + [bytes_to_long(rng(16)) for i in range(1, self.__k)]
        self._shamirPoly = np.polynomial.Polynomial(coefficients)

        return self._shamirPoly.coef

    def splitSecret(self, s):
        """
        Split the secret into shares
        :param s: secret
        :return: a list of shares
        """
        f = self.__polynomial(s)
        shares = [(x, np.polynomial.polynomial.polyval(x, f) % self.__p) for x in range(1, self.__n + 1)]
        return shares

    def reconstruct(self, shares):
        """
        Reconstruct the secret provided the minimum number of shares
        :param shares: a list of shares
        :return: secret
        """
        if len(shares) < self.__k:
            raise Exception("Provided shares are not enough to reconstruct")
        x = [a for a, b in shares]
        y = [b for a, b in shares]
        return self.__interpolate(x, y)

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


from utils import *

# Assume 10 parties with t = 4
parties = 10
t = 4
ui = [randNum() for i in range(parties)]
sss = SSS(parties, t)
uiShares = [sss.splitSecret(u) for u in ui]
ui_iShare = [uiShares[i][i][1] for i in range(parties)]
vander = vanderMatrix(parties, t)
ri = computeRandElem(vander, ui_iShare)
print(ri)
x = 2**512 -1
print(math.log(x,2))
print(math.log(x,2) / parties / 8)
print(rng(3))
