"""Exact certificates for a counterexample to Wu and Zhou's Problem 1.3.

Run with Python 3.9 or later. All calculations use integers. A direction
illuminates a vertex precisely when its scalar product with every active
outward facet normal is strictly negative.
"""

from functools import reduce
from itertools import combinations
from math import gcd


def require(condition, message):
    if not condition:
        raise ValueError(message)


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def scale(k, x):
    return tuple(k * a for a in x)


def subtract(x, y):
    return tuple(a - b for a, b in zip(x, y))


def determinant(matrix):
    """Laplace expansion. The largest matrices used here are 4 by 4."""
    if len(matrix) == 1:
        return matrix[0][0]
    result = 0
    for col, coefficient in enumerate(matrix[0]):
        if coefficient:
            minor = [row[:col] + row[col + 1:] for row in matrix[1:]]
            result += (-1) ** col * coefficient * determinant(minor)
    return result


def facets(vertices):
    """Enumerate supporting hyperplanes through d affinely independent points."""
    dim = len(vertices[0])
    found = set()
    for points in combinations(vertices, dim):
        rows = [subtract(p, points[0]) for p in points[1:]]
        normal = tuple(
            (-1) ** col * determinant([row[:col] + row[col + 1:] for row in rows])
            for col in range(dim)
        )
        divisor = reduce(gcd, normal, 0)
        if divisor == 0:
            continue
        normal = tuple(x // divisor for x in normal)
        bound = dot(normal, points[0])
        values = [dot(normal, p) for p in vertices]
        if max(values) == bound and min(values) < bound:
            found.add((normal, bound))
        elif min(values) == bound and max(values) > bound:
            found.add((scale(-1, normal), -bound))
    require(found, "No facets found")
    return sorted(found)


def check_upper_bound(vertices, groups):
    """Verify every claimed direction on all vertices assigned to it."""
    inequalities = facets(vertices)
    covered = set()
    for direction, group in groups:
        for vertex in group:
            active = [u for u, b in inequalities if dot(u, vertex) == b]
            require(active, f"No supporting facet at {vertex}")
            require(all(dot(u, direction) < 0 for u in active),
                    f"Direction {direction} misses {vertex}")
            covered.add(vertex)
    require(covered == set(vertices), "Some vertices are missing")
    return len(inequalities)


def opposite_supports(vertices, first, second, normal):
    """Opposite supports forbid one light from serving any point on each."""
    values = [dot(normal, p) for p in vertices]
    low, high = min(values), max(values)
    require(low < high, "Constant functional")
    require(all(dot(normal, p) == high for p in first), "Missed upper support")
    require(all(dot(normal, p) == low for p in second), "Missed lower support")


def check(n):
    e = [tuple(int(i == j) for j in range(n)) for i in range(n)]
    negative = [scale(-2, v) for v in e]
    base = e + negative
    top = [p + (1,) for p in base]
    bottom = [scale(-1, p) for p in top]
    lift = top + bottom

    # One light per negative vertex and one per pair of positive vertices.
    base_groups = [(scale(-1, p), [p]) for p in negative]
    for i in range(0, n, 2):
        group = e[i:i + 2]
        direction = tuple(-sum(coords) for coords in zip(*group))
        base_groups.append((direction, group))
    base_facets = check_upper_bound(base, base_groups)

    # One vertical light for all positive vertices in each layer.
    down = (0,) * n + (-1,)
    lift_groups = [(down, top[:n])]
    lift_groups.extend((scale(-1, p), [p]) for p in top[n:])
    lifted_top_groups = list(lift_groups)
    for direction, group in lifted_top_groups:
        lift_groups.append((scale(-1, direction), [scale(-1, p) for p in group]))
    lift_facets = check_upper_bound(lift, lift_groups)

    # Base lower bound. No light can mix signs or serve two negative vertices.
    opposite_supports(base, e, negative, (1,) * n)
    for i, j in combinations(range(n), 2):
        normal = subtract(e[j], e[i])
        opposite_supports(base, [negative[i]], [negative[j]], normal)

    # No light can serve three positive vertices. At each chosen vertex the
    # displayed supporting normal would require a strict negative dot product,
    # while the three normals have zero sum.
    for triple in combinations(range(n), 3):
        normals = []
        for i in triple:
            u = tuple(2 if k == i else -int(k in triple) for k in range(n))
            require(dot(u, e[i]) == max(dot(u, p) for p in base),
                    "Triple witness is not supporting")
            normals.append(u)
        require(all(sum(coords) == 0 for coords in zip(*normals)),
                "Triple witnesses do not sum to zero")
    base_lower = n + (n + 1) // 2

    # Lift lower bound. Layers need disjoint lights. Within each, positives
    # and negatives also need disjoint lights, and the n negatives are pairwise
    # incompatible. Central reflection checks the lower layer using -normal.
    opposite_supports(lift, top, bottom, (0,) * n + (1,))
    for sign, layer in [(1, top), (-1, bottom)]:
        opposite_supports(lift, layer[:n], layer[n:], scale(sign, (2,) * n + (1,)))
        for i, j in combinations(range(n), 2):
            normal = scale(sign, subtract(e[j], e[i]) + (0,))
            opposite_supports(lift, [layer[n + i]], [layer[n + j]], normal)
    lift_lower = 2 * (n + 1)

    require(len(base_groups) == base_lower, "Base bounds differ")
    require(len(lift_groups) == lift_lower, "Lift bounds differ")
    print(f"n={n}: I(T)={base_lower}, I(S)={lift_lower}, 2 I(T)={2 * base_lower}"
          f" | {base_facets} base facets, {lift_facets} lift facets | all checks passed")


if __name__ == "__main__":
    for base_dimension in (3, 4):
        check(base_dimension)
