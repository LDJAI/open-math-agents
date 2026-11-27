"""Exhaustively test all 64 labeled four-item inputs and all admissible oracle decisions."""
from itertools import combinations, permutations, product
from math import factorial


def test_instance(n, directions):
    edges = list(combinations(range(n), 2))
    rankings = list(permutations(range(n)))
    bits = [tuple(order.index(a) < order.index(b) for a, b in edges) for order in rankings]
    scores = [sum(a == b for a, b in zip(row, directions)) for row in bits]
    optimum = max(scores)
    bonus = len(edges) + 1
    base = 8 * factorial(n)
    tested_leaves = 0

    def run(prefix):
        nonlocal tested_leaves
        assert any(s == optimum and row[:len(prefix)] == prefix for row, s in zip(bits, scores))
        if len(prefix) == len(edges):
            tested_leaves += 1
            return
        weights = [base ** (s + bonus * sum(a == b for a, b in zip(row, prefix)))
                   for row, s in zip(bits, scores)]
        total = sum(weights)
        mass = sum(w for row, w in zip(bits, weights) if row[len(prefix)])
        # Allow even a tie at either endpoint of the oracle's error interval.
        if 4 * mass >= total:
            run(prefix + (True,))
        if 4 * (total - mass) >= total:
            run(prefix + (False,))

    run(())
    return tested_leaves


if __name__ == '__main__':
    n = 4
    instances = list(product([True, False], repeat=n * (n - 1) // 2))
    leaves = sum(test_instance(n, directions) for directions in instances)
    print(f'{len(instances)} tournaments, {leaves} compatible completed branch paths; every result optimal.')
