"""Construct bipartite graphs from matching numbers or check the parametrization."""

from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import combinations, product
from math import comb, perm
import json


def subsets(mask):
    """Yield nonempty submasks."""
    subset = mask
    while subset:
        yield subset
        subset = (subset - 1) & mask


def indices(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


@dataclass(frozen=True)
class Template:
    k: int
    left_cover_size: int
    core: tuple
    classes: tuple

    def coefficients(self):
        # A state is (occupied cover vertices, number of selected edges).
        terms = {(0, 0): 1}
        factors = [[(mask, 1, 1)] for mask in self.core]
        for mask, multiplicity in self.classes:
            factors.append([
                (subset, subset.bit_count(), perm(multiplicity, subset.bit_count()))
                for subset in subsets(mask) if subset.bit_count() <= multiplicity
            ])
        for factor in factors:
            updated = terms.copy()  # Choosing 1 in this factor.
            for (occupied, size), coefficient in terms.items():
                for mask, added, ways in factor:
                    if not occupied & mask:
                        state = (occupied | mask, size + added)
                        updated[state] = updated.get(state, 0) + ways * coefficient
            terms = updated
        counts = [0] * self.k
        for (_, size), coefficient in terms.items():
            if size:
                counts[size - 1] += coefficient
        return tuple(counts)

    def graph(self):
        """Return a JSON-compatible graph with independent left/right numbering."""
        a = self.left_cover_size
        left_size, right_size = a, self.k - a
        edges = []
        for mask in self.core:
            left, right = indices(mask)
            edges.append((left, right - a))
        for mask, multiplicity in self.classes:
            neighbors = indices(mask)
            for _ in range(multiplicity):
                if neighbors[0] < a:
                    edges.extend((left, right_size) for left in neighbors)
                    right_size += 1
                else:
                    edges.extend((left_size, right - a) for right in neighbors)
                    left_size += 1
        return {"left_size": left_size, "right_size": right_size, "edges": edges}


def classes_with_budget(types, budget):
    """Enumerate integer multiplicities with the prescribed total edge count."""
    if not budget:
        yield ()
        return
    for start, mask in enumerate(types):
        degree = mask.bit_count()
        for count in range(1, budget // degree + 1):
            for rest in classes_with_budget(types[start + 1:], budget - degree * count):
                yield ((mask, count),) + rest


def templates(edge_count, k):
    for a in range(k // 2 + 1):  # Transposition interchanges the two sides.
        left_indices = range(a)
        right_indices = range(a, k)
        possible_edges = [(1 << i) | (1 << j) for i in left_indices for j in right_indices]
        left_mask = (1 << a) - 1
        right_mask = ((1 << k) - 1) ^ left_mask
        types = tuple(subsets(left_mask)) + tuple(subsets(right_mask))
        for size in range(min(edge_count, len(possible_edges)) + 1):
            for core in combinations(possible_edges, size):
                for classes in classes_with_budget(types, edge_count - size):
                    yield Template(k, a, core, classes)


def realize(counts):
    """Return an explicit graph or None when the counts cannot occur."""
    counts = tuple(counts)
    if not counts:
        return {"left_size": 0, "right_size": 0, "edges": []}
    if any(type(x) is not int or x < 1 for x in counts):
        return None
    e, k = counts[0], len(counts)
    if k > e or any(count > comb(e, i) for i, count in enumerate(counts, 1)):
        return None
    for template in templates(e, k):
        if template.coefficients() == counts:
            return template.graph()
    return None


def literal_matchings(edges):
    """Independent oracle: inspect every edge subset directly."""
    counts = []
    for size in range(1, len(edges) + 1):
        count = 0
        for subgraph in combinations(edges, size):
            left, right = zip(*subgraph)
            if len(set(left)) == size and len(set(right)) == size:
                count += 1
        if not count:
            break
        counts.append(count)
    return tuple(counts)


def exhaustive_check(max_edges):
    square = list(product(range(max_edges), repeat=2))
    checked_boards = checked_vectors = 0
    for e in range(max_edges + 1):
        graphs = combinations(square, e)
        spectra = {literal_matchings(edges) for edges in graphs}
        checked_boards += comb(len(square), e)
        checked_vectors += len(spectra)
        generated = set()
        if e == 0:
            generated.add(())
        for k in range(1, e + 1):
            for template in templates(e, k):
                counts = template.coefficients()
                if counts[-1]:
                    generated.add(counts)
        assert generated == spectra, (e, generated ^ spectra)
        for counts in spectra:
            graph = realize(counts)
            assert graph is not None and literal_matchings(graph["edges"]) == counts
        print(f"{e} edges: {comb(len(square), e)} boards, {len(spectra)} vectors")
    # Exhaust the larger space of potential input vectors for e <= 4.
    accepted = rejected = 0
    for e in range(1, min(4, max_edges) + 1):
        expected = {literal_matchings(edges) for edges in combinations(square, e)}
        for k in range(1, e + 1):
            for tail in product(*(range(1, 1 + comb(e, i)) for i in range(2, k + 1))):
                counts = (e,) + tail
                graph = realize(counts)
                assert (graph is not None) == (counts in expected), counts
                if graph is None:
                    rejected += 1
                else:
                    accepted += 1
    print(f"Complete spectrum agreement: {checked_boards} boards, {checked_vectors} vectors.")
    print(f"Recognition input checks: {accepted} accepted, {rejected} rejected.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    solve = commands.add_parser("realize")
    solve.add_argument("counts", nargs="*", type=int)
    check = commands.add_parser("check")
    check.add_argument("--max-edges", default=5, type=int)
    args = parser.parse_args()
    if args.command == "check":
        exhaustive_check(args.max_edges)
    else:
        print(json.dumps(realize(args.counts)))
