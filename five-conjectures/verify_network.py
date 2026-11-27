"""Check the paper's distance identities by direct breadth-first search."""

from collections import deque
from itertools import combinations, product


def plane(q):
    points = list(product(range(q), range(q), [1]))
    points += [(r, 1, 0) for r in range(q)] + [(1, 0, 0)]
    n = len(points)
    return 2*n, {(i, n+j) for i, p in enumerate(points)
                 for j, line in enumerate(points)
                 if sum(x*y for x, y in zip(p, line)) % q == 0}


def near_pencil(m):
    # Label u,b_i first (point side); v,a_i last (line side).
    n = m+1
    return 2*n, {(u, v) for i in range(1, n)
                 for u, v in [(0, n+i), (i, n+i), (i, n)]}


def distances(adj, root, drop=(), add=()):
    graph = [neighbors.copy() for neighbors in adj]
    for u, v in drop:
        graph[u].remove(v)
        graph[v].remove(u)
    for u, v in add:
        graph[u].add(v)
        graph[v].add(u)
    d = [None] * len(adj)
    d[root] = 0
    todo = deque([root])
    while todo:
        u = todo.popleft()
        for v in graph[u]:
            if d[v] is None:
                d[v] = d[u]+1
                todo.append(v)
    assert None not in d
    return d


def check(label, geometry, order=None):
    size, edges = geometry
    adj = [set() for _ in range(size)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    weight = [1+(i*i+3*i+7) % 19 for i in range(size)]
    s = [2*weight[i]+sum(weight[j] for j in adj[i]) for i in range(size)]

    def cost(d):
        return sum(a*b for a, b in zip(d, weight))

    counts = [0, 0, 0]
    for u in range(size):
        baseline = cost(distances(adj, u))
        for v in adj[u]:
            for x in adj[v]-{u}:
                delta = cost(distances(adj, u, [(u, v)], [(u, x)]))-baseline
                assert delta == s[v]-s[x]-weight[u], (label, u, v, x)
                counts[0] += 1
    if order is not None:
        q = order
        points = list(range(size//2))
        lines = list(range(size//2, size))
        b = 5
        weight[size//2:] = [b]*len(lines)
        total_points = sum(weight[p] for p in points)
        for u in points:
            base = distances(adj, u)
            baseline = cost(base)
            drop = [(u, v) for v in adj[u]]
            for x in set(points)-{u}:
                new = distances(adj, u, drop, [(u, v) for v in adj[x]])
                assert cost(new) == baseline
                new = distances(adj, u, drop, [(u, x)])
                assert cost(new)-baseline == total_points-weight[u]-2*weight[x]+len(lines)*b
                counts[1] += 2
            # Represent the exterior neighbor by an extra pendant vertex. Other
            # attached parts need only be represented via their root's weight.
            ext = [neighbors.copy() for neighbors in adj] + [{u}]
            z = len(adj)
            ext[u].add(z)
            before = cost(distances(ext, z)[:-1])
            savings = []
            for line in set(lines)-adj[u]:
                after = cost(distances(ext, z, add=[(z, line)])[:-1])
                savings.append(before-after)
                counts[2] += 1
            assert len(savings) == q*q
            assert sum(savings) == q*(total_points-weight[u])+q*q*(q*q+2)*b
    return counts


def check_nonbipartite_example():
    vertices = [set(t) for t in combinations(range(7), 3)]
    n = len(vertices)
    adj = [{j for j, t in enumerate(vertices) if t.isdisjoint(v)} for v in vertices]
    # The disjointness graph has degree four and no cycles below length six.
    for u in range(n):
        assert len(adj[u]) == 4
        for v in adj[u]:
            assert distances(adj, u, drop=[(u, v)])[v] >= 5
    distance = [distances(adj, u) for u in range(n)]
    assert max(max(d) for d in distance) == 3
    assert any(distance[0][u] % 2 == distance[0][v] % 2 for u in range(n) for v in adj[u])
    for u in range(n):
        for v in range(n):
            if distance[u][v] == 3:
                assert sum(distance[first][v] == 2 for first in adj[u]) >= 2
    weights = [1+(i*i+3*i+7) % 19 for i in range(n)]
    s = [2*weights[i]+sum(weights[j] for j in adj[i]) for i in range(n)]
    count = 0
    for u in range(n):
        for v in adj[u]:
            for x in adj[v]-{u}:
                after = distances(adj, u, drop=[(u, v)], add=[(u, x)])
                delta = sum(w*(new-old) for w, new, old in zip(weights, after, distance[u]))
                assert delta <= s[v]-s[x]-weights[u]
                count += 1
    return count


if __name__ == "__main__":
    totals = [0, 0, 0]
    for name, graph, q in (
        [(f"PG(2,{p})", plane(p), p) for p in (2, 3, 5)]
        + [(f"near-pencil-{m}", near_pencil(m), None) for m in (2, 3, 5, 9)]
    ):
        counts = check(name, graph, q)
        print(name, *counts)
        totals = [a+b for a, b in zip(totals, counts)]
    print("swap identities, whole-pencil/replacement identities, pendant-link gains:", *totals)
    print("nonbipartite odd graph swap inequalities:", check_nonbipartite_example())
