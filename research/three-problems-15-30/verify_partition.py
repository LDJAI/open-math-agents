"""Exhaustive independent check on every labeled simple graph through six vertices."""
from itertools import combinations
from partition import tree_partition


def check_size(n):
    edges = tuple(combinations(range(n), 2))
    m = len(edges)
    count = [0] * (1 << m)
    parity = [0] * (1 << m)
    all_bits = (1 << n) - 1

    # Only n-1-edge connected sets are trees. Compute each tree's actual
    # bipartition by traversal, without using determinants or linear equations.
    for indices in combinations(range(m), n - 1):
        adj = [[] for _ in range(n)]
        mask = 0
        for k in indices:
            u, v = edges[k]
            adj[u].append(v)
            adj[v].append(u)
            mask |= 1 << k
        color = {0: 0}
        stack = [0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in color:
                    color[v] = color[u] ^ 1
                    stack.append(v)
        if len(color) == n:
            count[mask] = 1
            parity[mask] = sum(color[v] << v for v in color)

    # Subset zeta transform: each tree contributes once to every supergraph.
    for k in range(m):
        step = 1 << k
        for base in range(0, len(count), 2 * step):
            for lower in range(base, base + step):
                upper = lower + step
                count[upper] += count[lower]
                parity[upper] ^= parity[lower]

    even = odd = comparisons = 0
    for mask, trees in enumerate(count):
        if trees == 0:
            continue
        members = [edge for k, edge in enumerate(edges) if (mask >> k) & 1]
        for root in range(n):
            # Re-rooting each individual tree reverses the product globally
            # exactly when the aggregated bit at that root is one.
            expected = parity[mask] ^ (all_bits if (parity[mask] >> root) & 1 else 0)
            computed = tree_partition(n, members, root)
            actual = sum(bit << k for k, bit in enumerate(computed))
            if expected != actual:
                raise AssertionError((n, members, root, expected, actual))
            comparisons += 1
        if trees % 2:
            odd += 1
        else:
            even += 1
            assert parity[mask] == 0
    return odd, even, comparisons


if __name__ == "__main__":
    totals = [0, 0, 0]
    print("vertices  odd-tree-count  even-tree-count  graph/root comparisons")
    for n in range(1, 7):
        stats = check_size(n)
        print(f"{n:8d} {stats[0]:15d} {stats[1]:16d} {stats[2]:23d}")
        totals = [x + y for x, y in zip(totals, stats)]
    print(f"PASS: {sum(totals[:2])} connected labeled graphs, {totals[2]} graph/root comparisons.")
