"""Independent exact checks for MO 128755. Standard-library Python 3."""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product
from math import comb


def bitstrings(length):
    return product((0, 1), repeat=length)


def enumerate_words(n, shifts):
    """Joint mismatch counts from every assignment of pattern and text bits."""
    histogram = Counter()
    for pattern in bitstrings(n):
        for text in bitstrings(n + max(shifts)):
            distances = tuple(sum(a ^ text[t + shift] for t, a in enumerate(pattern))
                              for shift in shifts)
            histogram[distances] += 1
    return histogram


def row_transfer(n, k):
    """Count the same assignments while grouping complementary text suffixes."""
    suffix_mask = (1 << (k - 1)) - 1
    initial = (0,) * k
    states = Counter((min(s, suffix_mask ^ s), initial) for s in range(suffix_mask + 1))
    for _ in range(n):
        updated = Counter()
        for (s, distances), multiplicity in states.items():
            for b in (0, 1):
                block = (s << 1) | b
                suffix = block & suffix_mask
                representative = min(suffix, suffix_mask ^ suffix)
                for a in (0, 1):
                    new_distances = tuple(d + (a ^ ((block >> (k - 1 - i)) & 1))
                                          for i, d in enumerate(distances))
                    updated[representative, new_distances] += multiplicity
        states = updated
    result = Counter()
    for (_, distances), multiplicity in states.items():
        result[distances] += multiplicity
    return result


def cycle_basis(n, shifts):
    """Fundamental cycle basis as bit masks of edges, grouped by shift."""
    edges = [(t, n + t + shift) for shift in shifts for t in range(n)]
    size = 2 * n + max(shifts)
    parents = list(range(size))
    tree = [[] for _ in parents]
    basis = []

    def root(v):
        while parents[v] != v:
            v = parents[v]
        return v

    for index, (u, v) in enumerate(edges):
        a, b = root(u), root(v)
        edge = 1 << index
        if a != b:
            parents[a] = b
            tree[u].append((v, edge))
            tree[v].append((u, edge))
            continue
        queue = deque([(u, -1, edge)])
        while queue:
            node, previous, mask = queue.popleft()
            if node == v:
                basis.append(mask)
                break
            queue.extend((other, node, mask ^ bit)
                         for other, bit in tree[node] if other != previous)
    return basis


def binomial(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def coefficient_tail(n, r, h):
    if h == 0:
        return sum(comb(n, j) for j in range(r, n + 1))
    return -sum((-1) ** j * binomial(h - 1, j) * binomial(n - h, r - 1 - j)
                for j in range(r))


def cycle_tails(n, shifts):
    """Return P(all selected window distances are at least r), for r=1,...,n."""
    k = len(shifts)
    basis = cycle_basis(n, shifts)
    even_subgraphs = [0]
    for mask in basis:
        even_subgraphs.extend([g ^ mask for g in even_subgraphs])
    result = [0] * n
    for mask in even_subgraphs:
        counts = [((mask >> (i * n)) & ((1 << n) - 1)).bit_count() for i in range(k)]
        for r in range(1, n + 1):
            value = 1
            for h in counts:
                value *= coefficient_tail(n, r, h)
            result[r - 1] += value
    return [Fraction(t, 1 << (n * k)) for t in result]


def check():
    tested = 0
    for n in range(1, 5):
        for k in range(1, 6):
            shifts = list(range(k))
            raw = enumerate_words(n, shifts)
            assert raw == row_transfer(n, k), (n, k, "transfer")
            total = raw.total()
            exact_tails = [Fraction(sum(v for d, v in raw.items() if min(d) >= r), total)
                           for r in range(1, n + 1)]
            assert exact_tails == cycle_tails(n, shifts), (n, k, "cycle formula")
            tested += 1
    print(f"Full joint transfer and cycle-tail checks passed for {tested} consecutive-window pairs (n,k).")
    tested = 0
    for n in (1, 2, 3):
        for count in range(1, 5):
            for shifts in combinations(range(5), count):
                raw = enumerate_words(n, shifts)
                independent = all(v * (1 << (n * count)) ==
                                  raw.total() * product_binomials(n, distances)
                                  for distances in product(range(n + 1), repeat=count)
                                  for v in [raw[distances]])
                assert independent == (not cycle_basis(n, shifts)), (n, shifts, "forest")
                tested += 1
    print(f"Independence criterion passed for {tested} arbitrary shift sets and lengths.")
    for n, k in ((2, 2), (2, 3), (3, 4), (4, 5)):
        tails = cycle_tails(n, list(range(k)))
        print(f"n={n}, k={k}: E[X]={sum(tails)}, tails={', '.join(map(str, tails))}")


def product_binomials(n, distances):
    result = 1
    for d in distances:
        result *= comb(n, d)
    return result


if __name__ == "__main__":
    check()
