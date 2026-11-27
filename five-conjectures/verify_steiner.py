"""Check a signed certificate for the lifted Steiner flow formulation.

Usage: python3 verify_steiner.py [degree ...]
The degree counts the number of literal factors multiplying an LP constraint.
Python's integers represent exact truth tables over all canonical trees.
"""

import argparse
from itertools import combinations


def make_graph(hubs):
    """Return adjacency and the terminal for every pair of hubs."""
    root = hubs
    pair_terminals = {
        pair: root + 1 + i
        for i, pair in enumerate(combinations(range(hubs), 2))
    }
    adjacency = {v: set() for v in range(root + 1 + len(pair_terminals))}
    for h in range(hubs):
        adjacency[root].add(h)
        adjacency[h].add(root)
    for (i, j), v in pair_terminals.items():
        for h in (i, j):
            adjacency[h].add(v)
            adjacency[v].add(h)
    return root, pair_terminals, adjacency


def exact_integer_optimum(hubs, root, terminals, adjacency):
    """A connected induced vertex set has a spanning tree with |V|-1 edges."""
    for size in range(hubs + 1):
        for hub_set in combinations(range(hubs), size):
            available = {root, *terminals, *hub_set}
            visited = {root}
            stack = [root]
            while stack:
                for v in adjacency[stack.pop()] & available - visited:
                    stack.append(v)
                    visited.add(v)
            if visited == available:
                return len(visited) - 1
    raise AssertionError("the graph is connected")


def verify(degree):
    denominator = degree + 2
    hubs = 2 * denominator
    root, pair_terminals, adjacency = make_graph(hubs)
    terminals = set(pair_terminals.values())
    optimum = exact_integer_optimum(hubs, root, terminals, adjacency)

    # State 0 keeps every hub, state h+1 omits hub h.
    full_mask = (1 << (hubs + 1)) - 1
    arcs = [(u, v) for u in adjacency for v in adjacency[u]]
    installed = {a: 0 for a in arcs}
    flows = {t: {a: 0 for a in arcs} for t in terminals}
    for state in range(hubs + 1):
        omitted = state - 1
        bit = 1 << state
        for h in range(hubs):
            if h != omitted:
                installed[root, h] |= bit
        for (i, j), t in pair_terminals.items():
            chosen = j if omitted == i else i
            installed[chosen, t] |= bit
            flows[t][root, chosen] |= bit
            flows[t][chosen, t] |= bit

    def numerator(mask):
        # denominator * signed expectation of an event
        base = denominator - hubs if mask & 1 else 0
        return base + (mask >> 1).bit_count()

    objective = sum(map(numerator, installed.values()))
    assert objective == denominator * (optimum - 1)
    literal_masks = {0, full_mask}
    slack_masks = set()
    for arc in arcs:
        z = installed[arc]
        literal_masks.update((z, full_mask ^ z))
        for t in terminals:
            f = flows[t][arc]
            assert f & ~z == 0
            slack_masks.add(z ^ f)  # z-f takes values in {0,1}.
            literal_masks.update((f, full_mask ^ f))
    slack_masks.update(literal_masks)  # all variable bounds

    # Conservation is an equality on each tree. Every lifted equality follows.
    for state in range(hubs + 1):
        for t in terminals:
            divergence = {v: 0 for v in adjacency}
            for (u, v), f in flows[t].items():
                if f & (1 << state):
                    divergence[u] += 1
                    divergence[v] -= 1
            assert all(
                value == int(v == root) - int(v == t)
                for v, value in divergence.items()
            )

    # Intersections sharing a truth table give the same lifted constraint.
    event_masks = {full_mask}
    for _ in range(degree):
        event_masks = {e & literal for e in event_masks for literal in literal_masks}
    assert all(numerator(e & slack) >= 0 for e in event_masks for slack in slack_masks)
    print(
        f"degree={degree} hubs={hubs} vertices={len(adjacency)} "
        f"terminal_count={len(terminals) + 1} exact_optimum={optimum} "
        f"certified_relaxation_value={objective // denominator} "
        f"distinct_multiplier_truth_tables={len(event_masks)}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degrees", type=int, nargs="*", default=[0, 1, 2, 3])
    args = parser.parse_args()
    if any(d < 0 for d in args.degrees):
        parser.error("degrees must be nonnegative")
    for d in args.degrees:
        verify(d)
