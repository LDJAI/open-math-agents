"""Construct edge-disjoint routes for an ordered demand chain on a capacitated ring."""

from itertools import product
from typing import Iterator


def cycle_routes(capacities: tuple[int, ...], terminals: tuple[int, ...]) -> list[int]:
    """Return link masks; parallel physical copies are assigned by order of use."""
    n = len(capacities)
    if n < 3 or not terminals or min(capacities) < 0:
        raise ValueError("Need a ring of at least three links and a nonempty terminal list")
    if any(not 0 <= t < n for t in terminals):
        raise ValueError("Terminal outside the ring")
    k = len(terminals) - 1
    low, second = sorted(capacities)[:2]
    if low + second < k:
        raise ValueError("Ring edge connectivity is below the number of demands")
    full = (1 << n) - 1
    arcs = []
    for start, finish in zip(terminals, terminals[1:]):
        arc = 0
        here = start
        while here != finish:
            arc |= 1 << here
            here = (here + 1) % n
        arcs.append(arc)

    # Ignore requests already at their destination. Other arcs have two choices.
    reverse = [full ^ arc if arc else 0 for arc in arcs]
    e = capacities.index(low)

    def orientation_key(routes: list[int]) -> tuple[int, int]:
        loads = [sum((arc >> f) & 1 for arc in routes) for f in range(n)]
        return loads[e], max(loads)

    chosen = min([arcs, reverse], key=orientation_key).copy()
    crossing = [i for i, arc in enumerate(chosen) if (arc >> e) & 1]
    for i in crossing[:max(0, len(crossing) - low)]:
        chosen[i] ^= full
    return chosen


def verify(capacities: tuple[int, ...], terminals: tuple[int, ...], routes: list[int]) -> None:
    """Reconstruct each route edge by edge. Check continuity, endpoints and capacities."""
    n = len(capacities)
    assert len(routes) + 1 == len(terminals)
    loads = [0] * n
    for start, finish, arc in zip(terminals, terminals[1:], routes):
        remaining = arc
        here = start
        while remaining:
            candidates = [((here - 1) % n, (here - 1) % n), (here, (here + 1) % n)]
            available = [(edge, nxt) for edge, nxt in candidates if (remaining >> edge) & 1]
            assert len(available) == 1
            edge, here = available[0]
            remaining ^= 1 << edge
            loads[edge] += 1
        assert here == finish
    assert all(load <= cap for load, cap in zip(loads, capacities))


def minimal_capacities(n: int, k: int) -> Iterator[tuple[int, ...]]:
    """Every k-connected integer-capacity ring dominates one of these vectors."""
    uniform = ((k + 1) // 2,) * n
    yield uniform
    for e in range(n):
        for cap in range((k + 1) // 2):
            yield tuple(cap if i == e else k - cap for i in range(n))


def exhaustive_test() -> None:
    cases = 0
    for n, max_hops in [(3, 7), (4, 7), (5, 6), (6, 4)]:
        for k in range(1, max_hops + 1):
            for steps in product(range(1, n), repeat=k):
                # Rotational symmetry permits fixing the initial terminal.
                terminals = [0]
                for step in steps:
                    terminals.append((terminals[-1] + step) % n)
                for cap in minimal_capacities(n, k):
                    routes = cycle_routes(cap, tuple(terminals))
                    verify(cap, tuple(terminals), routes)
                    cases += 1
    # Repeated successive terminals are omitted by the router.
    cap = (2, 3, 4, 3)
    repeated = (2, 2, 1, 2, 1, 1)
    verify(cap, repeated, cycle_routes(cap, repeated))
    print(f"{cases:,} enumerated instances passed, plus the consecutive-repeat regression.")


if __name__ == "__main__":
    exhaustive_test()
