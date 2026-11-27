"""Finite regression check for the local auction notes. Python standard library only."""

from functools import cache
from itertools import product


@cache
def mechanism(bids, retained, cap):
    """Each bidder is a vector of nonnegative bids, with 0 representing no edge."""
    choices = [[] for _ in bids]
    for item in retained:
        claims = sorted(
            ((value[item], -buyer) for buyer, value in enumerate(bids) if value[item]),
            reverse=True,
        )
        if not claims or len(claims) > cap:
            continue
        high, negative_owner = claims[0]
        price = claims[1][0] if len(claims) > 1 else 0
        choices[-negative_owner].append((high - price, -item, price))

    outcomes = []
    for options in choices:
        if options:
            _, negative_item, price = max(options)
            outcomes.append((-negative_item, price))
        else:
            outcomes.append((None, 0))
    return tuple(outcomes)


def utility(true_type, outcome):
    item, price = outcome
    return (0 if item is None else true_type[item]) - price


def welfare(types, outcomes):
    return sum(values[j] for values, (j, _) in zip(types, outcomes) if j is not None)


@cache
def matchings(buyers, items):
    """Enumerate assignments directly, independently of bids and the auction."""
    return tuple(
        assignment
        for assignment in product((None,) + items, repeat=buyers)
        if len([j for j in assignment if j is not None])
        == len({j for j in assignment if j is not None})
    )


def optimum(types, items):
    return max(
        sum(bids[j] for bids, j in zip(types, assignment) if j is not None)
        for assignment in matchings(len(types), tuple(items))
    )


def check_choices(types, true_outcome, reports, items, cap):
    assigned = [item for item, _ in true_outcome if item is not None]
    assert len(set(assigned)) == len(assigned)
    total = 0
    for i, true_type in enumerate(types):
        best = utility(true_type, true_outcome[i])
        assert best >= 0
        for lie in reports:
            if lie == true_type:
                continue
            changed = types[:i] + (lie,) + types[i + 1:]
            assert utility(true_type, mechanism(changed, items, cap)[i]) <= best
            total += 1
    return total


def main():
    items = (0, 1, 2)
    buyers = 3
    k = 2
    reports = tuple(
        r for r in product((0, 1, 2), repeat=len(items))
        if sum(v > 0 for v in r) <= k and len(set(r) - {0}) <= 1
    )
    checks = 0
    profiles = 0
    tight = False
    for types in product(reports, repeat=buyers):
        for cap in (1, 2, 3):
            out = mechanism(types, items, cap)
            eligible = tuple(j for j in items if sum(r[j] > 0 for r in types) <= cap)
            optimal = optimum(types, eligible)
            achieved = welfare(types, out)
            assert k * achieved >= optimal
            tight |= cap == 3 and optimal > 0 and k * achieved == optimal
            checks += check_choices(types, out, reports, items, cap)
        profiles += 1
    assert tight
    print(f"Uniform-buyer values: {profiles} profiles, {checks} deviations across 3 caps, tight example found.")

    items = (0, 1)
    reports = tuple(product((0, 1, 3), repeat=2))
    subsets = ((), (0,), (1,), (0, 1))
    checks = 0
    profiles = 0
    for types in product(reports, repeat=buyers):
        welfare_sum = 0
        for kept in subsets:
            out = mechanism(types, kept, buyers)
            checks += check_choices(types, out, reports, kept, buyers)
            welfare_sum += welfare(types, out)
        # With p=1/2 and k=2 the guarantee is 1/4 of optimum.
        # The four equally likely subset welfares must therefore add to at least OPT.
        assert welfare_sum >= optimum(types, items)
        profiles += 1
    print(f"Item-specific values: {profiles} profiles, all 4 retention sets, {checks} deviations.")


if __name__ == "__main__":
    main()
