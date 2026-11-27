"""Exact finite regression checks for the MAX-CUT norm construction."""
from itertools import product


def graph_cut(edges, sides):
    return sum(sides[u] != sides[v] for u, v in edges)


def ordered_edges(v):
    return [(u, w) for w in range(v) for u in range(w)]


def check(v):
    edges = ordered_edges(v)
    n = len(edges)
    base = [8*n - 3*j + 3 for j in range(1, n + 1)]
    alpha = 8*n + 1
    cuts = list(product(range(2), repeat=v-1))
    cuts = [(0,) + side for side in cuts]
    weight_vectors = []
    for side in cuts:
        bits = [int(side[u] != side[w]) for u, w in edges]
        weights = [b + c - prev for b, c, prev in zip(base, bits, [0] + bits[:-1])]
        assert min(weights) * 2 > alpha
        assert all(w > w_next for w, w_next in zip(weights, weights[1:]))
        assert weights[0] <= alpha
        weight_vectors.append(weights)
    assert max(w[0] for w in weight_vectors) == alpha
    cases = 0
    for graph_bits in product(range(2), repeat=n):
        graph = [e for e, included in zip(edges, graph_bits) if included]
        diagonal = [sum(graph_bits[j:]) for j in range(n)]
        optimum = max(graph_cut(graph, side) for side in cuts)
        hard_norm_times_alpha = max(sum(w*s for w,s in zip(weights, diagonal))
                                    for weights in weight_vectors)
        assert hard_norm_times_alpha - sum(b*s for b,s in zip(base, diagonal)) == optimum
        assert hard_norm_times_alpha**2 >= alpha**2 * sum(s*s for s in diagonal)
        assert (hard_norm_times_alpha**2 == alpha**2 * sum(s*s for s in diagonal)) == (sum(s > 0 for s in diagonal) <= 1)
        cases += 1
    return cases


if __name__ == '__main__':
    count = sum(check(v) for v in range(2, 6))
    print(f'Passed exact cut encoding, weight and rank-one checks for {count} labelled graphs on 2 through 5 vertices.')
