"""Exhaustive checks for the documented Paley(67) shortlist obstruction."""

from collections import Counter
from itertools import combinations
from math import comb


def main():
    order = 67
    vertices = range(order)
    residues = {i * i % order for i in range(1, order)}
    predecessors = [
        sum(1 << w for w in vertices if (v - w) % order in residues)
        for v in vertices
    ]
    all_vertices = (1 << order) - 1

    def missed(chosen):
        common = all_vertices
        for v in chosen:
            common &= predecessors[v]
        return common

    prescribed = (0, 1, 2, 5)
    witnesses = (13, 32, 43, 46, 53)
    assert missed(prescribed) == sum(1 << w for w in witnesses)
    assert all(missed((*prescribed, v)) for v in vertices)
    assert missed((0, 1, 2, 3, 20)) == 0
    assert missed((22, 59, 60, 62)) == 1  # The sole missed vertex is zero.

    # Translation by any residue preserves all edges. It suffices to check
    # four-sets containing zero, then count their four possible origins.
    counts_at_zero = Counter()
    for a, b, c in combinations(range(1, order), 3):
        remainder = missed((0, a, b, c))
        assert remainder, "A four-set already dominates the tournament."
        # Reusing one of the four vertices cannot cover a nonempty remainder.
        additions = sum((remainder & predecessors[v]) == 0 for v in vertices)
        counts_at_zero[additions] += 1

    counts = {}
    for additions, subtotal in counts_at_zero.items():
        quotient, residue = divmod(subtotal * order, 4)
        assert residue == 0
        counts[additions] = quotient
    assert sum(counts.values()) == comb(order, 4)
    assert counts[0] == 69_278
    print("Paley(67) has domination number 5.")
    print(f"{counts[0]:,} of {comb(order, 4):,} four-sets have no completion.")
    print("Completion counts (additions, number of four-sets):", sorted(counts.items()))


if __name__ == "__main__":
    main()
