"""Check the mixed-factorial-moment identity on every market of size at most 3."""
from fractions import Fraction
from itertools import permutations, product
from math import factorial


def falling(n, r):
    return factorial(n) // factorial(n - r) if r <= n else 0


def moments(n):
    # Each row gives a ranking by candidate, with smaller ranks preferred.
    orders = tuple(permutations(range(n)))
    matchings = [(p, tuple(p.index(b) for b in range(n))) for p in orders]
    totals = {(r, j): 0 for r in range(n + 1) for j in range(3)}
    for profile in product(orders, repeat=2 * n):
        men, women = profile[:n], profile[n:]
        fixed = sum(men[a][b] == women[b][a] == 0 for a in range(n) for b in range(n))
        count = sum(
            not any(
                men[a][b] < men[a][matching[a]] and women[b][a] < women[b][inverse[b]]
                for a in range(n) for b in range(n)
            )
            for matching, inverse in matchings
        )
        for r, j in totals:
            totals[r, j] += falling(fixed, r) * count**j
    return {key: Fraction(v, len(orders)**(2 * n)) for key, v in totals.items()}


if __name__ == "__main__":
    tables = [moments(n) for n in range(4)]
    for n in range(1, 4):
        for (r, j), actual in tables[n].items():
            expected = Fraction(falling(n, r)**2, n**(2*r)) * tables[n-r][0, j]
            assert actual == expected, (n, r, j, actual, expected)
        print(f"n={n}: {factorial(n)**(2*n)} profiles, all three moments pass")
