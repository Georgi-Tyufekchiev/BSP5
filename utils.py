import math

import numpy as np
from Crypto.Random import get_random_bytes as rng
from Crypto.Util.number import bytes_to_long


def vanderMatrix(N, t):
    """
    Make a Vandermonde matrix of size n x (n - t)
    :param N: Number of parties
    :param t: Threshold
    :return: vander matrix
    """
    x = np.array([n for n in range(1, N+1)])
    n = N - t
    return np.vander(x, n, increasing=True)


def computeVanderElem(vander, shares):
    """
    Compute [r1...r(n-t)] = M(s1...sn)
    :param vander: vander matrix
    :param shares: shares of parties
    :return: [r1...r(n-t)]
    """
    s = [shares[i][1] for i in range(len(shares))]
    return np.dot(np.transpose(vander), s)


def challenge(parties):
    x = 2 ** 512 - 1
    entropyBytes = math.floor((math.log(x, 2) / parties / 8))
    challenges = [bytes_to_long(rng(entropyBytes)) for _ in range(parties)]
    return challenges
