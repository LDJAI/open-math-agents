"""Reference counter and reproducible tests for MathOverflow 104415.

Run with Python 3.10 or later: python verify.py
An edge is (u, v, positive integer weight), with endpoints in range(n).
Trial division here is for the small test labels. The proof note specifies
the preprocessing model for the asymptotic algorithm.
"""
from itertools import combinations, product
from math import gcd, isqrt, log2, prod
from random import Random


def squarefree_divisors_with_sign(weight):
    """List (product, Möbius sign) for each subset of the prime support."""
    if weight < 1:
        raise ValueError("edge weights must be positive")
    divisors = [(1, 1)]
    residual = weight
    prime = 2
    while prime <= isqrt(residual):
        if residual % prime == 0:
            divisors += [(d * prime, -sign) for d, sign in divisors]
            while residual % prime == 0:
                residual //= prime
        prime = 3 if prime == 2 else prime + 2
    if residual > 1:
        divisors += [(d * residual, -sign) for d, sign in divisors]
    return divisors


def lift_graph(n, edges):
    """Build the signed lift with one node (original vertex, divisor)."""
    index = {}
    signs = []
    neighbors = []
    divisors = {}
    seen = set()

    def node(vertex, divisor, sign):
        key = (vertex, divisor)
        if key not in index:
            index[key] = len(signs)
            signs.append(sign)
            neighbors.append(set())
        return index[key]

    for u, v, weight in edges:
        if not (0 <= u < n and 0 <= v < n and u != v):
            raise ValueError("invalid endpoints")
        key = (min(u, v), max(u, v))
        if key in seen:
            raise ValueError("parallel edges")
        seen.add(key)
        if weight not in divisors:
            divisors[weight] = squarefree_divisors_with_sign(weight)
        support = divisors[weight]
        us = [node(u, d, sign) for d, sign in support]
        vs = [node(v, d, sign) for d, sign in support]
        for i in us:
            neighbors[i].update(vs)
        for j in vs:
            neighbors[j].update(us)
    return neighbors, signs


def matrix_sum(a, b, sign=1):
    return [[x + sign * y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def quadrants(m):
    h = len(m) // 2
    return ([r[:h] for r in m[:h]], [r[h:] for r in m[:h]],
            [r[:h] for r in m[h:]], [r[h:] for r in m[h:]])


def strassen(a, b):
    """Multiply square integer matrices of equal power-of-two size."""
    n = len(a)
    if n <= 8:
        cols = list(zip(*b))
        return [[sum(x * y for x, y in zip(r, c)) for c in cols] for r in a]
    aa, ab, ac, ad = quadrants(a)
    ba, bb, bc, bd = quadrants(b)
    p1 = strassen(matrix_sum(aa, ad), matrix_sum(ba, bd))
    p2 = strassen(matrix_sum(ac, ad), ba)
    p3 = strassen(aa, matrix_sum(bb, bd, -1))
    p4 = strassen(ad, matrix_sum(bc, ba, -1))
    p5 = strassen(matrix_sum(aa, ab), bd)
    p6 = strassen(matrix_sum(ac, aa, -1), matrix_sum(ba, bb))
    p7 = strassen(matrix_sum(ab, ad, -1), matrix_sum(bc, bd))
    tl = matrix_sum(matrix_sum(matrix_sum(p1, p4), p5, -1), p7)
    tr = matrix_sum(p3, p5)
    bl = matrix_sum(p2, p4)
    br = matrix_sum(matrix_sum(matrix_sum(p1, p2, -1), p3), p6)
    return [x + y for x, y in zip(tl, tr)] + [x + y for x, y in zip(bl, br)]


def heavy_triangle_sum(neighbors, signs, heavy):
    """Trace((D A)^3)/6 for the subgraph induced by the heavy vertices."""
    if len(heavy) < 3:
        return 0
    index = {u: i for i, u in enumerate(heavy)}
    order = 1 << (len(heavy) - 1).bit_length()
    matrix = [[0] * order for _ in range(order)]
    for i, u in enumerate(heavy):
        for v in neighbors[u]:
            if v in index:
                matrix[i][index[v]] = signs[u]
    square = strassen(matrix, matrix)
    trace = sum(square[i][j] * matrix[j][i]
                for i in range(len(heavy)) for j in range(len(heavy)))
    assert trace % 6 == 0
    return trace // 6


def signed_triangle_sum(neighbors, signs, threshold=None):
    """Count each triangle with the product of its three vertex signs."""
    if threshold is None:
        m = sum(map(len, neighbors)) // 2
        omega = log2(7)
        threshold = max(1, int(m ** ((omega - 1) / (omega + 1))))
    is_light = [len(row) <= threshold for row in neighbors]
    total = 0
    for v, row in enumerate(neighbors):
        if is_light[v]:
            # The smallest-index light vertex owns the triangle.
            eligible = (u for u in row if not is_light[u] or v < u)
            for u, w in combinations(eligible, 2):
                if w in neighbors[u]:
                    total += signs[v] * signs[u] * signs[w]
    heavy = [u for u, light in enumerate(is_light) if not light]
    return total + heavy_triangle_sum(neighbors, signs, heavy)


def count_valid(n, edges):
    return signed_triangle_sum(*lift_graph(n, edges))


def gcd_oracle(n, edges):
    weights = {(min(u, v), max(u, v)): w for u, v, w in edges}
    count = 0
    for u, v, w in combinations(range(n), 3):
        try:
            a, b, c = weights[u, v], weights[v, w], weights[u, w]
        except KeyError:
            continue
        count += gcd(a, b) == gcd(b, c) == gcd(c, a) == 1
    return count


def three_ov_check(left, middle, right, primes):
    """Check the reduction on three lists of bitmasks, including repetitions."""
    n_left, n_middle, n_right = len(left), len(middle), len(right)
    base_middle = n_left
    base_right = n_left + n_middle

    def support_product(bits):
        return prod(p for j, p in enumerate(primes) if bits & (1 << j))

    edges = []
    for i, a in enumerate(left):
        for j, b in enumerate(middle):
            edges.append((i, base_middle + j, support_product(a & b)))
    for j in range(n_middle):
        for k, c in enumerate(right):
            edges.append((base_middle + j, base_right + k, support_product(c)))
    for k in range(n_right):
        for i in range(n_left):
            edges.append((base_right + k, i, 1))
    expected = sum((a & b & c) == 0 for a in left for b in middle for c in right)
    assert count_valid(n_left + n_middle + n_right, edges) == expected


def test_three_ov():
    rng = Random(3104415)
    small_primes = (2, 3, 5, 7, 11)
    count = 0
    # All bit vectors in each class, with empty support and full support.
    for dim in range(4):
        vectors = range(1 << dim)
        three_ov_check(vectors, vectors, vectors, small_primes[:dim])
        count += 1
    for dim in range(1, 6):
        primes = small_primes[:dim]
        full = (1 << dim) - 1
        cases = [
            ([full] * 2, [full] * 3, [full] * 4),
            ([full] * 2, [0] * 3, [full] * 4),
            ([], [full, 0], [0]),
        ]
        for _ in range(8):
            cases.append(tuple([rng.randrange(1 << dim) for _ in range(rng.randrange(1, 5))]
                               for _ in range(3)))
        for parts in cases:
            three_ov_check(*parts, primes)
            count += 1
    print(f"3-OV reduction: {count} exhaustive-family, boundary and seeded cases matched")


def run_tests():
    rng = Random(104415)
    pairs = list(combinations(range(4), 2))
    exhaustive = 0
    for values in product((0, 1, 2, 3, 6), repeat=len(pairs)):
        edges = [(u, v, w) for (u, v), w in zip(pairs, values) if w]
        assert count_valid(4, edges) == gcd_oracle(4, edges), values
        exhaustive += 1
    print(f"Exhaustive four-vertex labeled graphs: {exhaustive} matched")

    sparse_dense = 0
    for n in range(3, 12):
        for density in (0, .12, .5, .88, 1):
            for labels in ((1,), (2, 4, 8), (2, 3, 5, 7, 11),
                           (1, 4, 9, 25, 6, 35, 42)):
                edges = [(u, v, rng.choice(labels)) for u, v in combinations(range(n), 2)
                         if rng.random() < density]
                expected = gcd_oracle(n, edges)
                rng.shuffle(edges)
                edges = [(v, u, w) if rng.random() < .5 else (u, v, w)
                         for u, v, w in edges]
                neighbors, signs = lift_graph(n, edges)
                max_degree = max(map(len, neighbors), default=0)
                for cutoff in (None, 0, 1, max_degree // 2, max_degree):
                    assert signed_triangle_sum(neighbors, signs, cutoff) == expected
                sparse_dense += 1
    print(f"Seeded graph cases: {sparse_dense} matched at five heavy/light thresholds")

    # Test signed counting independently of the arithmetic lift.
    for n in range(3, 26):
        signs = [rng.choice((-1, 1)) for _ in range(n)]
        neighbors = [set() for _ in range(n)]
        for u, v in combinations(range(n), 2):
            if rng.random() < .6:
                neighbors[u].add(v)
                neighbors[v].add(u)
        expected = sum(signs[u] * signs[v] * signs[w]
                       for u, v, w in combinations(range(n), 3)
                       if v in neighbors[u] and w in neighbors[v] and u in neighbors[w])
        for cutoff in (None, 0, n // 2, n):
            assert signed_triangle_sum(neighbors, signs, cutoff) == expected
    print("Independent signed graphs: 23 matched at four heavy/light thresholds")

    assert count_valid(0, []) == count_valid(1, []) == 0
    assert count_valid(3, [(0, 1, 1), (1, 2, 1), (2, 0, 1)]) == 1
    assert count_valid(3, [(0, 1, 30), (1, 2, 42), (2, 0, 70)]) == 0
    assert count_valid(3, [(0, 1, 2**40), (1, 2, 3**25), (2, 0, 5**21)]) == 1
    print("Empty, all-unit, cancellation, and high prime-power checks passed")


if __name__ == "__main__":
    run_tests()
    test_three_ov()
