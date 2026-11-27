"""Compute the product of all rooted spanning-tree bipartitions of a simple graph."""
import argparse
from collections.abc import Iterable


def tree_partition(n: int, edges: Iterable[tuple[int, int]], root: int = 0) -> tuple[int, ...]:
    """Return one color bit per vertex, normalized to zero at root.

    Vertices are numbered 0 to n-1. The graph must be simple and connected.
    Singletons are allowed. The returned bits encode signs by 0=+1 and 1=-1.
    """
    if n < 1 or not 0 <= root < n:
        raise ValueError("Require n >= 1 and a root between 0 and n-1.")
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v or v in neighbors[u]:
            raise ValueError("Expected distinct, undirected, loopless edges on the given vertices.")
        neighbors[u].add(v)
        neighbors[v].add(u)

    reached = {root}
    stack = [root]
    while stack:
        for v in neighbors[stack.pop()]:
            if v not in reached:
                reached.add(v)
                stack.append(v)
    if len(reached) != n:
        raise ValueError("The graph must be connected.")

    # The final bit of each row is the right-hand side, the vertex degree mod 2.
    vertices = [v for v in range(n) if v != root]
    index = {v: k for k, v in enumerate(vertices)}
    size = len(vertices)
    matrix = []
    for k, v in enumerate(vertices):
        degree_bit = len(neighbors[v]) % 2
        row = (degree_bit << k) | (degree_bit << size)
        for u in neighbors[v]:
            if u != root:
                row |= 1 << index[u]
        matrix.append(row)

    for col in range(size):
        pivot = next((r for r in range(col, size) if (matrix[r] >> col) & 1), None)
        if pivot is None:
            # Even spanning-tree count implies an identically zero product coloring.
            return (0,) * n
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        for r in range(size):
            if r != col and (matrix[r] >> col) & 1:
                matrix[r] ^= matrix[col]

    color = [0] * n
    for k, v in enumerate(vertices):
        color[v] = (matrix[k] >> size) & 1
    return tuple(color)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="number of vertices")
    parser.add_argument("edges", nargs="*", help="undirected edges, for example 0,1 1,2")
    parser.add_argument("--root", type=int, default=0)
    args = parser.parse_args()
    try:
        pairs = [tuple(map(int, edge.split(","))) for edge in args.edges]
        print(*tree_partition(args.n, pairs, args.root))
    except ValueError as error:
        parser.error(str(error))
