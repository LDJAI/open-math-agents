"""Count all agendas by the published Banks-tree recurrence, using integer arithmetic."""
from itertools import permutations
from math import factorial

# Bit j is set if candidate j beats i in the original tournament.
BEATEN_BY = (178, 88, 131, 37, 44, 198, 29, 90)
EXPECTED_BEFORE = (4200, 7560, 9240, 10080, 3780, 2940, 2520, 0)
EXPECTED_AFTER = (1260, 7308, 13860, 13356, 0, 2016, 2520, 0)


def counts(beaten_by):
    n = len(beaten_by)
    for i in range(n):
        assert not beaten_by[i] & (1 << i)
        for j in range(i):
            assert bool(beaten_by[i] & (1 << j)) != bool(beaten_by[j] & (1 << i))

    def banks(order):
        if len(order) == 1:
            return order[0]
        # The left child deletes position 2. The right child deletes position 1.
        left = banks(order[:1] + order[2:])
        right = banks(order[1:])
        return right if beaten_by[left] & (1 << right) else left

    result = [0] * n
    for order in permutations(range(n)):
        result[banks(order)] += 1
    assert sum(result) == factorial(n)
    return tuple(result)


def tournament(ballots):
    labels = "ABCDEFGH"
    for ballot in ballots:
        assert sorted(ballot) == list(labels)
    return tuple(
        sum(1 << j for j, opponent in enumerate(labels)
            if sum(ballot.index(opponent) < ballot.index(candidate) for ballot in ballots)
            > len(ballots) // 2)
        for candidate in labels
    )


def main():
    ballots = ["BHCFEADG", "GFDEHBAC", "ACDEGBHF"]
    assert tournament(ballots) == BEATEN_BY
    ballots[0] = ballots[0].replace("AD", "DA")
    after = list(BEATEN_BY)
    assert after[3] & 1
    assert not after[0] & (1 << 3)
    after[3] -= 1
    after[0] += 1 << 3
    assert tournament(ballots) == tuple(after)
    before_counts = counts(BEATEN_BY)
    after_counts = counts(after)
    print("Before", before_counts)
    print("After ", after_counts)
    assert before_counts == EXPECTED_BEFORE
    assert after_counts == EXPECTED_AFTER
    assert before_counts.index(max(before_counts)) == 3 and before_counts.count(max(before_counts)) == 1
    assert after_counts.index(max(after_counts)) == 2 and after_counts.count(max(after_counts)) == 1


if __name__ == "__main__":
    main()
