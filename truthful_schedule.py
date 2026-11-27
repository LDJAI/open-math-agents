"""Truthful public scheduling for two approval sets with rational endpoints.

Import schedule(A, B). Each report is a nonempty iterable of interval pairs.
Integers, strings such as "1/3", and Fraction instances work as endpoints.
Run this file directly to check the local rule and some interval examples.
"""

from bisect import bisect_right
from fractions import Fraction
from itertools import product
from random import Random

WIDTH = Fraction(1, 3)
SLOTS = range(3)


def _normalize(intervals):
    """Sort intervals and join overlaps and touching endpoints."""
    merged = []
    for left, right in sorted((Fraction(a), Fraction(b)) for a, b in intervals):
        if not 0 <= left < right <= 1:
            raise ValueError("Each interval must satisfy 0 <= left < right <= 1.")
        if merged and left <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(right, merged[-1][1]))
        else:
            merged.append((left, right))
    if not merged:
        raise ValueError("A report must include at least one interval.")
    return merged


def nominee(approved):
    for i in SLOTS:
        if approved[i] and approved[(i + 1) % 3]:
            return i
    return next((i for i in SLOTS if approved[i]), 0)


def winners(first, second):
    i, j = nominee(first), nominee(second)
    return (i, j) if i != j else (i, (i + 1) % 3)


def schedule(first, second):
    """Return the common schedule as sorted, disjoint closed intervals."""
    reports = [_normalize(first), _normalize(second)]
    starts = [[left for left, _ in report] for report in reports]
    cuts = {Fraction(0), WIDTH}
    for report in reports:
        for interval in report:
            cuts.update(endpoint % WIDTH for endpoint in interval)
    cuts = sorted(cuts)

    def approves(person, point):
        index = bisect_right(starts[person], point) - 1
        return index >= 0 and point <= reports[person][index][1]

    chosen = []
    for left, right in zip(cuts, cuts[1:]):
        middle = (left + right) / 2
        ballots = [tuple(approves(person, middle + i * WIDTH) for i in SLOTS)
                   for person in range(2)]
        for i in winners(*ballots):
            chosen.append((left + i * WIDTH, right + i * WIDTH))
    return _normalize(chosen)


def _length(intervals):
    return sum((right - left for left, right in intervals), Fraction(0))


def _overlap(first, second):
    """Inputs here are normalized, with disjoint interiors."""
    return sum((max(0, min(b, d) - max(a, c))
                for a, b in first for c, d in second), Fraction(0))


def _self_test():
    ballots = list(product([False, True], repeat=3))
    for a, b in product(ballots, repeat=2):
        chosen = winners(a, b)
        assert len(set(chosen)) == 2
        assert set(chosen) == set(winners(b, a))
        truthful = sum(a[i] for i in chosen)
        assert 2 * truthful >= sum(a)
        for x in ballots:
            assert sum(a[i] for i in winners(x, b)) <= truthful

    a, b = [(0, 2 * WIDTH)], [(2 * WIDTH, 1)]
    outcome = schedule(a, b)
    assert outcome == [(0, WIDTH), (2 * WIDTH, 1)]
    assert _overlap(a, outcome) == _length(a) / 2

    striped = [(i * WIDTH, i * WIDTH + WIDTH / 2) for i in SLOTS]
    compact = [(0, Fraction(1, 2))]
    assert _overlap(striped, schedule(striped, striped)) == WIDTH
    assert _overlap(compact, schedule(compact, compact)) == Fraction(1, 2)

    rng = Random(312603)

    def random_report():
        ends = sorted(rng.sample(range(61), 2 * rng.randint(1, 8)))
        return [(Fraction(l, 60), Fraction(r, 60)) for l, r in zip(ends[::2], ends[1::2])]

    for _ in range(250):
        a, b, x = (random_report() for _ in range(3))
        outcome = schedule(a, b)
        assert _length(outcome) == 2 * WIDTH
        assert outcome == schedule(b, a)
        assert 2 * _overlap(a, outcome) >= _length(a)
        assert 2 * _overlap(b, outcome) >= _length(b)
        assert _overlap(a, schedule(x, b)) <= _overlap(a, outcome)
        assert _overlap(b, schedule(a, x)) <= _overlap(b, outcome)

    print("64 local truth/other pairs and all 512 deviations pass.")
    print("The tight half-share and position-dependent examples pass.")
    print("250 exact rational interval examples pass, including deviations by each voter.")


if __name__ == "__main__":
    _self_test()
