"""Verify rational identities and bracket the maximizing noise variance exactly."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement


def quantities(priors, t):
    m = sum(priors, Q(0)) / len(priors)
    k = [m / b - 1 for b in priors]
    w = [1 + x*t for x in k]
    g = sum(x*(2+x*t)/v**2 for x, v in zip(k, w))
    dg = -sum(x*x*(3+x*t)/v**3 for x, v in zip(k, w))
    d = len(k)*t - sum(t/v for v in w)
    derivative = len(k) - sum(1/v**2 for v in w)
    assert derivative == t*g
    if 0 < t < 1:
        a = m*t/(1-t)
        assert m*d == len(k)*a*m/(a+m) - sum(a*b/(a+b) for b in priors)
    return d, g, dg


def verify():
    n = 0
    for length in range(2, 6):
        for b in combinations_with_replacement(map(Q, (1, 2, 4, 9)), length):
            if len(set(b)) == 1:
                continue
            d0, g0, _ = quantities(b, Q(0))
            d1, g1, _ = quantities(b, Q(1))
            assert d0 == d1 == 0 and g0 > 0 > g1
            for i in range(1, 8):
                d, _, dg = quantities(b, Q(i, 8))
                assert d > 0 and dg < 0
            n += 1
    print(f"Exact rational checks passed for {n} nonconstant lists.")
    b = (Q(1), Q(9))
    lo, hi = Q(0), Q(1)
    m = sum(b)/len(b)
    for _ in range(60):
        mid = (lo+hi)/2
        if quantities(b, mid)[1] > 0:
            lo = mid
        else:
            hi = mid
    a0, a1 = (m*t/(1-t) for t in (lo, hi))
    print(f"Example, priors 1 and 9: noise variance {float(a0):.12f}, "
          f"bracket width {float(a1-a0):.3g}; "
          f"total variance gap {float(m*quantities(b, lo)[0]):.12f}.")


if __name__ == "__main__":
    verify()
