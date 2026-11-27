"""Exact greedy and unrestricted-deviation checks for the two labelled profiles."""
from collections import deque

PROFILES = [
    (15, [(0, 2, 2), (0, 4, 0), (0, 6, 6), (1, 3, 1), (1, 5, 5),
          (1, 8, 8), (2, 3, 2), (4, 5, 5), (6, 7, 6), (7, 8, 8)],
     [3, 3, 4, 4, 7, 7], 6, (14, 14), 14),
    (20, [(0, 2, 2), (0, 5, 5), (0, 8, 8), (1, 4, 4), (1, 7, 7),
          (1, 10, 10), (2, 3, 2), (3, 4, 4), (5, 6, 5), (6, 7, 7),
          (8, 9, 8), (9, 10, 10)], [3, 3, 3, 6, 6, 6, 9, 9, 9],
     8, (22, 30), 24)
]


def distances(adj, start):
    result = [None] * len(adj)
    result[start] = 0
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if result[v] is None:
                result[v] = result[u] + 1
                queue.append(v)
    return result


def distance_sum(adj, u):
    d = distances(adj, u)
    return None if None in d else sum(d)


def best_deviation(adj, u, old, price):
    """All purchased-neighbor sets, including those that join to pendant nodes.

    For a target v, distance > k iff the buyer has no neighbor within distance
    k-1 of v in the graph with the buyer removed. These are disjointness
    predicates; the subset sum transform computes all objective values.
    """
    n = len(adj)
    baseline = distance_sum(adj, u) + price * len(old)
    penalties = baseline + n * n + n * price + 1
    free = adj[u] - old
    choices = sorted(set(range(n)) - free - {u})
    bit = {j: 1 << k for k, j in enumerate(choices)}
    count = 1 << len(choices)
    costs = [0] * count
    smaller = [neighbors - {u} for neighbors in adj]
    smaller[u] = set()
    for target in set(range(n)) - {u}:
        d = distances(smaller, target)
        within = 0
        for radius in range(-1, n-1):
            if any(d[v] is not None and d[v] <= radius for v in free):
                break
            for j in choices:
                if d[j] == radius:
                    within |= bit[j]
            costs[within] += 1
        else:
            # For a disconnected choice, every purchasable member of the
            # target's component is absent, and no free neighbor reaches it.
            costs[within] += penalties
    jump = 1
    while jump < count:
        for start in range(jump, count, 2 * jump):
            for k in range(start, start + jump):
                costs[k] += costs[k-jump]
        jump *= 2
    def cost(mask):
        return price * mask.bit_count() + costs[(count-1) ^ mask]
    assert cost(sum(bit[j] for j in old)) == baseline
    mask = min(range(count), key=cost)
    selected = {j for j in choices if bit[j] & mask}
    # Independent BFS confirms the minimizing purchase set.
    changed = [s.copy() for s in adj]
    for j in old ^ selected:
        if j in old:
            changed[u].remove(j)
            changed[j].remove(u)
        else:
            changed[u].add(j)
            changed[j].add(u)
    assert cost(mask) == distance_sum(changed, u) + price * len(selected)
    return baseline - cost(mask), sorted(selected), count


def check(profile):
    n, core, parents, expected_girth, expected_interval, price = profile
    edges = [*core, *((p, j, p) for j, p in enumerate(parents, n-len(parents)))]
    adj = [set() for _ in range(n)]
    owned = [set() for _ in range(n)]
    for a, b, owner in edges:
        assert owner in (a, b) and b not in adj[a]
        adj[a].add(b)
        adj[b].add(a)
        owned[owner].add(a if owner == b else b)

    cycles = []
    for a, b, _ in edges:
        adj[a].remove(b)
        adj[b].remove(a)
        d = distances(adj, a)[b]
        if d is not None:
            cycles.append(d + 1)
        adj[a].add(b)
        adj[b].add(a)
    assert min(cycles) == expected_girth
    # Displayed price-independent two-for-two deviations.
    deviator, dropped, bought, before, after = (
        (8, (1, 7), (3, 6), 35, 34) if n == 15
        else (10, (1, 9), (3, 5), 55, 53)
    )
    assert set(dropped) <= owned[deviator] and not set(bought) & adj[deviator]
    replacement = [s.copy() for s in adj]
    for j in dropped:
        replacement[deviator].remove(j)
        replacement[j].remove(deviator)
    for j in bought:
        replacement[deviator].add(j)
        replacement[j].add(deviator)
    assert distance_sum(adj, deviator) == before
    assert distance_sum(replacement, deviator) == after
    low = 0
    high = n * n
    greedy_checks = 0
    improvements = []
    total = 0
    for u in range(n):
        old = owned[u]
        base = distance_sum(adj, u)
        new = set(range(n)) - adj[u] - {u}
        for drop, add in [(None, j) for j in new] + [(j, None) for j in old] + [
                (a, b) for a in old for b in new]:
            if drop is not None:
                adj[u].remove(drop)
                adj[drop].remove(u)
            if add is not None:
                adj[u].add(add)
                adj[add].add(u)
            newcost = distance_sum(adj, u)
            if newcost is not None:
                if drop is None:
                    low = max(low, base - newcost)
                elif add is None:
                    high = min(high, newcost - base)
                else:
                    assert newcost >= base
            if add is not None:
                adj[u].remove(add)
                adj[add].remove(u)
            if drop is not None:
                adj[u].add(drop)
                adj[drop].add(u)
            greedy_checks += 1
        gain, chosen, possibilities = best_deviation(adj, u, old, price)
        if gain > 0:
            improvements.append((u, gain, sorted(old), chosen))
        total += possibilities
    assert (low, high) == expected_interval and improvements
    print(f'n={n} girth={min(cycles)} greedy_price_interval=[{low},{high}] '
          f'greedy_checks={greedy_checks} all_strategies={total} price={price}')
    print('strictly improving best responses (buyer, saving, old, new)', improvements)


if __name__ == '__main__':
    for item in PROFILES:
        check(item)
