"""Exact finite checks for the orthogonal-rounding examples, standard Python only."""
from fractions import Fraction
from itertools import permutations, product


def reflection(size):
    return [[Fraction(int(i == j)) - Fraction(2, size)
             for j in range(size)] for i in range(size)]


def determinant(matrix):
    remaining = [row[:] for row in matrix]
    sign = 1
    result = Fraction(1)
    for k in range(len(remaining)):
        pivot = next((i for i in range(k, len(remaining)) if remaining[i][k]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != k:
            remaining[k], remaining[pivot] = remaining[pivot], remaining[k]
            sign *= -1
        pivot_row = remaining[k]
        result *= pivot_row[k]
        for i in range(k + 1, len(remaining)):
            scale = remaining[i][k] / pivot_row[k]
            remaining[i] = [x - scale * y for x, y in zip(remaining[i], pivot_row)]
    return sign * result


def verify_matrix(matrix, expected_trace, expected_det):
    n = len(matrix)
    assert all(sum(a * b for a, b in zip(matrix[i], matrix[j])) == int(i == j)
               for i in range(n) for j in range(n))
    assert determinant(matrix) == expected_det
    assert sum(matrix[i][i] for i in range(n)) == expected_trace
    assert all(matrix[i][i] > abs(matrix[i][j]) for i in range(n)
               for j in range(n) if j != i)


def main():
    size = 5
    matrix = reflection(size)
    verify_matrix(matrix, size - 2, -1)
    best, minimizers, count = None, [], 0
    for perm in permutations(range(size)):
        for signs in product((-1, 1), repeat=size):
            overlap = sum(s * matrix[i][j] for i, (j, s) in enumerate(zip(perm, signs)))
            distance_squared = 2 * size - 2 * overlap
            count += 1
            if best is None or distance_squared < best:
                best, minimizers = distance_squared, []
            if distance_squared == best:
                minimizers.append((perm, signs))
    assert best == 4
    assert minimizers == [(tuple(range(size)), (1,) * size)]
    block = [[matrix[i % size][j % size] if i // size == j // size else Fraction(0)
              for j in range(2 * size)] for i in range(2 * size)]
    verify_matrix(block, 2 * (size - 2), 1)
    print(f"5 × 5 witness: {count} signed permutations, unique minimizer I, squared distance 4.")
    print("10 × 10 witness: orthogonal, determinant +1, trace 6, unique closest signed permutation I.")


if __name__ == "__main__":
    main()
