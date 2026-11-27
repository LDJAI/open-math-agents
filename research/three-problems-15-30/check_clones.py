"""Check every labeled two-clone ranking in eight complete three-item tournaments."""
from fractions import Fraction
from itertools import combinations, permutations, product


def check(directions, decisions):
    n, count = 3, 2
    edges = list(combinations(range(n), 2))
    clones = list(product(range(n), range(count)))
    transversals = list(product(range(count), repeat=n))
    q = Fraction(4, 3)

    def payoff(e, direction):
        return int(direction == directions[e]) + int(direction == decisions.get(e))

    def score(order):
        return sum(payoff(e, order.index(i) < order.index(j)) for e, (i, j) in enumerate(edges))

    best = max(map(score, permutations(range(n))))
    best_cloned = -1
    masses = {(e, a, b): 0 for e in range(len(edges)) for a, b in product(range(count), repeat=2)}
    for order in permutations(clones):
        positions = {clone: i for i, clone in enumerate(order)}
        seen = {(e, a, b): positions[i, a] < positions[j, b]
                for e, (i, j) in enumerate(edges) for a, b in product(range(count), repeat=2)}
        cloned = sum(payoff(e, forward) for (e, a, b), forward in seen.items())
        best_cloned = max(cloned, best_cloned)
        total_score = sum(score(sorted(range(n), key=lambda i: positions[i, representatives[i]]))
                          for representatives in transversals)
        assert total_score * count ** 2 == cloned * len(transversals)
        weight = q ** cloned
        for entry, forward in seen.items():
            if forward:
                masses[entry] += weight
    assert best_cloned == count ** 2 * best
    for e in range(len(edges)):
        assert len({masses[e, a, b] for a, b in product(range(count), repeat=2)}) == 1


if __name__ == '__main__':
    count = 0
    for directions in product([False, True], repeat=3):
        for prefix in [(), (False,), (True,), (False, True)]:
            check(directions, dict(enumerate(prefix)))
            count += 1
    print(f'{count} weighted models; 720 clone rankings and 8 representatives each; '
          f'{count*720:,} Gibbs states, {count*720*8:,} representative selections; '
          'every score identity, optimum, and exchangeability check passed.')
