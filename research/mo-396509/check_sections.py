"""Exact, independent finite checks for the planar comparison in the manuscript.

Run with Python 3.10 or later. All vertices, intersections and integrals are rational.
The enumeration is a check of the proof and covers a finite set of examples only.
"""

from fractions import Fraction as Q
from itertools import combinations, permutations, product


def cross(a, b):
    return a[0] * b[1] - b[0] * a[1]


def turn(a, b, c):
    return cross((b[0] - a[0], b[1] - a[1]), (c[0] - a[0], c[1] - a[1]))


def hull(points):
    points = sorted(set(points))

    def half(seq):
        part = []
        for point in seq:
            while len(part) >= 2 and turn(part[-2], part[-1], point) <= 0:
                part.pop()
            part.append(point)
        return part[:-1]

    return half(points) + half(reversed(points))


def clip(polygon, side):
    """Intersect the polygon with side(vertex) >= 0."""
    out = []
    for a, b in zip(polygon, polygon[1:] + polygon[:1]):
        sa, sb = side(*a), side(*b)
        if sa >= 0:
            out.append(a)
        if sa * sb < 0:
            t = sa / (sa - sb)
            out.append(tuple(x + t * (y - x) for x, y in zip(a, b)))
    return out


def integral(polygon, linear):
    """Integrate a linear form over the polygon using signed triangles with apex 0."""
    return sum((cross(a, b) * (linear(*a) + linear(*b)) / 6
                for a, b in zip(polygon, polygon[1:] + polygon[:1])), Q(0))


def orbit(gaps):
    u, v = gaps
    centered = (-2*u-v, u-v, u+2*v)
    return {(Q(b-a), Q(c-b)) for a, b, c in permutations(centered)}


def evaluate(orbits):
    region = hull(set().union(*orbits))
    region = clip(clip(region, lambda u, v: u), lambda u, v: v)
    right = clip(region, lambda u, v: u-v)
    left = clip(region, lambda u, v: v-u)
    imbalance = integral(right, lambda u, v: u-v) + integral(left, lambda u, v: v-u)
    spread = integral(region, lambda u, v: u+v)
    assert spread > 0
    return imbalance / spread


def main():
    orbits = [orbit(g) for g in product(range(5), repeat=2) if g != (0, 0)]
    ratios = [evaluate(group) for size in (1, 2, 3) for group in combinations(orbits, size)]
    assert max(ratios) == Q(5, 9)
    assert evaluate([orbit((0, 1))]) == evaluate([orbit((1, 0))]) == Q(5, 9)
    print(f'{len(ratios)} orbit selections checked. Maximum imbalance/range = {max(ratios)}.')

    # At unit rate E[min(X,Z)] = 1/2. Conditional on M=(X+Y)/2,
    # E[min(M,Z)|M] = 1-exp(-M) and E[exp(-M)] = (1+1/2)^(-2).
    spread = 2 - 2*Q(1, 2)
    midpoint_error = 2 - 2*(1 - (1 + Q(1, 2))**-2)
    assert (spread, midpoint_error, (spread-midpoint_error)/spread) == (1, Q(8, 9), Q(1, 9))
    print(f'Unit exponential: spread = {spread}, midpoint error = {midpoint_error}, gain = {spread-midpoint_error}.')


if __name__ == '__main__':
    main()
