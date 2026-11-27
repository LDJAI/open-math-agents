"""Exact pairwise marginal for a Babington Smith ranking model with rational inputs."""
from fractions import Fraction
from itertools import permutations
from math import prod


def partition(weights):
    """Sum the ranking weights by deleting the last item of each subset."""
    n = len(weights)
    size = 1 << n
    inbound = [[Fraction(1)] * size for _ in range(n)]
    for last in range(n):
        for subset in range(1, size):
            bit = subset & -subset
            predecessor = bit.bit_length() - 1
            inbound[last][subset] = inbound[last][subset ^ bit] * weights[predecessor][last]
    totals = [Fraction(0)] * size
    totals[0] = Fraction(1)
    for subset in range(1, size):
        candidates = subset
        while candidates:
            bit = candidates & -candidates
            last = bit.bit_length() - 1
            preceding = subset ^ bit
            totals[subset] += totals[preceding] * inbound[last][preceding]
            candidates ^= bit
    return totals[-1]


def marginal(matrix, first, second):
    """Return Pr(first precedes second); matrix entries can be Fraction objects."""
    weights = [list(map(Fraction, row)) for row in matrix]
    n = len(weights)
    if not (0 <= first < n and 0 <= second < n and first != second):
        raise ValueError('the queried items must be distinct valid indices')
    if any(len(row) != n for row in weights):
        raise ValueError('expected a square pairwise probability matrix')
    if any(not (0 < weights[i][j] < 1 and weights[i][j] + weights[j][i] == 1)
           for i in range(n) for j in range(i + 1, n)):
        raise ValueError('off-diagonal probabilities must be positive and reciprocal')
    total = partition(weights)
    weights[second][first] = Fraction(0)
    return partition(weights) / total


if __name__ == '__main__':
    for n in range(2, 7):
        weights = [[Fraction(1, 2) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                weights[i][j] = Fraction(2 + ((i + 3*j) % 5), 8)
                weights[j][i] = 1 - weights[i][j]
        distribution = {s: prod(weights[s[i]][s[j]] for i in range(n) for j in range(i+1,n))
                        for s in permutations(range(n))}
        for a in range(n):
            for b in range(a + 1, n):
                before = sum(w for s, w in distribution.items() if s.index(a) < s.index(b))
                assert marginal(weights, a, b) == before / sum(distribution.values())
    print('35 marginals for n=2 through n=6 agree exactly with permutation enumeration.')
