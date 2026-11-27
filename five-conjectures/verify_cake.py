"""Exact arithmetic checks for the witness and role-switch constructions in README.md."""
from fractions import Fraction as F


def value_at(points, x):
    for (lo, flo), (hi, fhi) in zip(points, points[1:]):
        if lo <= x <= hi:
            return flo + (fhi - flo) * (x - lo) / (hi - lo)
    raise ValueError("point outside interval")


def first_cut(points, alpha):
    for (lo, flo), (hi, fhi) in zip(points, points[1:]):
        if flo == alpha:
            return lo
        if min(flo, fhi) <= alpha <= max(flo, fhi):
            return lo + (hi - lo) * (alpha - flo) / (fhi - flo)
    raise ValueError("target not attained")


def main():
    half = F(1, 2)
    endpoints = [(F(0), F(0)), (F(1), F(1))]
    samples = [F(1, 13), F(1, 3), F(1, 2), F(3, 4), F(12, 13)]
    checked = 0
    for mark in samples:
        for other_mark in samples:
            if other_mark == mark:
                continue
            witnesses = [F(1, 8), F(3, 8)] if other_mark < mark else [F(5, 8), F(7, 8)]
            assert {F(1, 4) <= z <= F(3, 4) for z in witnesses} == {False, True}
            for signed_value in witnesses:
                points = sorted(endpoints + [(mark, half), (other_mark, signed_value)])
                assert first_cut(points, half) == mark
                assert value_at(points, other_mark) == signed_value
                checked += 1
    print(f"Role-switch witness checks: {checked}")

    a, first, true_second, fake_second, b = map(
        F, ["1/10", "1/3", "11/20", "7/10", "4/5"]
    )
    lie = sorted(endpoints + [(a, a), (first, first), (fake_second, true_second)])
    assert first_cut(lie, F(1, 3)) == first
    assert value_at(lie, a) == a
    assert first_cut(lie, (1 + value_at(lie, a)) / 2) == fake_second
    assert true_second < fake_second < b
    assert fake_second - true_second == F(3, 20)
    print(f"Public-history gain for three agents: {fake_second - true_second}")


if __name__ == "__main__":
    main()
