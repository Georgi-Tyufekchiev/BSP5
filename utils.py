import numpy as np


def vanderMatrix(N, t):
    """
    Make a Vandermonde matrix of size n x (n - t)
    :param N: Number of parties
    :param t: Threshold
    :return: vander matrix
    """
    x = np.array([n for n in range(N)])
    n = N - t
    return np.vander(x, n)


def computeRandElem(vander, shares):
    """
    Compute [r1...r(n-t)] = M(s1...sn)
    :param vander: vander matrix
    :param shares: shares of parties
    :return: [r1...r(n-t)]
    """
    return np.dot(np.transpose(vander), shares)
