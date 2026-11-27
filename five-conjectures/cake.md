# Mixed cake division with two agents

Research note, November 26, 2026

Josué Ortega and Erel Segal-Halevi conjectured that a Robertson–Webb mechanism cannot make a connected, proportional division of a mixed cake while satisfying not-obvious manipulability (NOM). The conjecture appears in §7 of their [2020 working paper](https://www.econstor.eu/bitstream/10419/271235/1/qms-rp2020-04.pdf) and §7.2 of the [journal paper](https://doi.org/10.1007/s00355-022-01416-4). The following construction proves existence for two agents. For every finite group size, a separate [full public scalar-query construction](cake-scalar.md) addresses the original normalized, signed model.

## A four-query protocol

The cake is the unit interval. Each agent has an additive finite nonatomic signed valuation with total value 1, as normalized in §3.1 of the paper. Write F_i(x) for the value of the prefix ending at x. Each F_i is continuous, with endpoints 0 and 1. A truthful cut gives the first point at which the requested cumulative value is attained. All reports are public once the simultaneous round ends. Each agent gets a single interval.

1. Each agent simultaneously reports the first point m_i at which F_i reaches 1/2. These marks are interior. If the marks coincide, split there and give the prefix to agent 1.
2. Otherwise each agent simultaneously reports z_i = F_i(m_j), an evaluation at the other agent's mark. Set b_i to 1 if z_i lies in [1/4,3/4] and 0 otherwise. This bit records whether both sides receive at least one quarter in the agent’s evaluation. Designate agent 1 the chooser if the two bits agree, and agent 2 otherwise.
3. Cut at the nonchooser's mark. Give the chooser the prefix if her report there is at least 1/2, and the suffix otherwise. The other agent receives the remainder.

The protocol uses two simultaneous rounds and at most four standard queries. Its only numerical operations after the queries are comparisons and the role-selection rule.

## Why either role remains possible

Fix any distinct interior marks m and x. There are strictly increasing cumulative valuations whose first half mark is m and that assign each possible bit to x. For x<m, prescribe F(x) as either 1/8 or 3/8. For x>m, prescribe either 5/8 or 7/8. In each case prescribe F(0)=0, F(m)=1/2, F(1)=1, and interpolate linearly between these points in spatial order. The result is a normalized finite nonatomic valuation with first crossing at m. If the domain requires some strictly negative parts, insert a small downwards excursion away from the prescribed points without introducing a premature half crossing. Consequently an opponent can induce either role even after both marks have been publicly revealed.

## Proof

**Proportionality.** Against any consistent reports of the opponent, a truthful agent either cuts at her own half mark or chooses the better side of her opponent's cut. Either way her utility is at least 1/2. With two agents and a full partition this also gives envy-freeness, since her valuation of the other share is 1 minus her valuation of her own.

**Second round.** Fix a consistent true valuation, both distinct marks, and the other agent's mark x. If the agent becomes the nonchooser, either side at her own mark is worth exactly 1/2 to her. If she becomes the chooser, her report can yield at most B(x) = max(F_i(x),1-F_i(x)). Truthful play realizes B(x) in the chooser role. The role lemma lets the opponent assign her either role for every one of her possible reports. Truth thus guarantees 1/2 and has best case B(x). Every deviation has worst case at most 1/2 and best case at most B(x). This proves both NOM inequalities at this node.

**First round, best case.** Across all complete connected allocations into two pieces, the largest utility the agent can receive is U = max over x in [0,1] of B(x). For every interior x distinct from her own mark, an opponent can declare x truthfully as its first half mark and realize whichever bit at her mark makes her chooser. This gives her B(x). Continuity shows her truthful supremum is U even if the maximizing x is an endpoint or her mark. Every lie produces an endpoint piece, whose value is at most U.

**First round, worst case.** Against an opponent with exactly her own true valuation, truthful play by that opponent guarantees the opponent at least half, regardless of her deviation. The two pieces sum to 1 under that same valuation. Every deviation therefore has worst-case utility at most half. Truth guarantees half. These are all decision nodes.

## Scope and strategic interpretation

The same protocol works when valuations are all nonnegative or may be signed. An agent’s report of whether the other cut is reasonably balanced helps determine who gets to choose. Neither side needs private randomness, an encoded full valuation, or an optimization query. The proof establishes the supremum and infimum requirements of NOM. Individual deviations can still pay off against particular opponents. The mechanism and the proof use the two-agent fact that either side of a cut at one's own half mark is equally valuable. This fact does not apply to the division among the remaining n-1 agents if n exceeds two.

## A public-history counterexample to the published leftmost-leaves theorem

There is a separate issue with the positive-valuation theorem (§§4–5 of the journal paper). In the paper's explicit public-history extensive form, three all-positive agents suffice for a manipulation that raises the next-round utility against every opponent consistent with the public record.

Suppose the three first-round one-third marks are 1/10, 1/3, and 4/5. Agent A is uniform and has the middle mark. Agent B has the last mark. These reports can arise from strictly positive piecewise-constant densities, for example by linear interpolation from (0,0) through each prescribed mark with value 1/3 to (1,1). The first agent receives the prefix up to 1/10. For B the next mark is the first y such that F_B(y) = (1+F_B(1/10))/2. Nonnegativity makes this target at least 1/2, strictly above F_B(4/5)=1/3. Consequently B's second mark is strictly beyond 4/5, for every consistent type.

A's truthful second mark is 11/20, the midpoint of [1/10,1], and her realized utility is 9/20. If she reports 7/10 instead, she still wins and receives 3/5. This raises both her conditional best case and her conditional worst case by 3/20. The deviation is dynamically consistent: use the strictly increasing piecewise linear cumulative valuation through (0,0), (1/10,1/10), (1/3,1/3), (7/10,11/20), and (1,1). It preserves even a separate public evaluation of the remaining cake.

The argument relies on §3.2, where edges distinguish every combination of answers and participants observe the whole previous history. If only the winning mark is revealed, the specific inference about B's next mark is unavailable. This counterexample concerns that theorem's public-history formulation. It does not settle the authors' general mixed-cake conjecture. A literature check under the paper's title, the mechanism's name, correction, public history, and losing cuts found no correction establishing priority for this observation. Neither result in this note has undergone external review.

The same obstruction applies to **every n ≥ 3**. Choose a first winning mark a in (0,1/n). The uniform agent has first mark 1/n, and each of the other n−2 surviving agents marks b, with t < b < 1 and t = a+(1-a)/(n-1). Each such survivor has F(b)=1/n. Its next cumulative target F(a)+(1-F(a))/(n-1) is at least 1/(n-1)>1/n, so its next cut must lie past b. The uniform agent wins with its truthful mark t or with any alternative mark d in (t,b), earning exactly d-t more from the deviation for every consistent continuation. Interpolation through (0,0), (a,a), (1/n,1/n), (d,t), and (1,1) gives a strictly increasing type consistent with every prior reply.

## Removing the total-value normalization for two agents

The construction also extends to arbitrary finite signed totals, including zero, if empty pieces are allowed. A separate initial round asks each agent to evaluate the whole cake. Let their reported totals be T_1,T_2 and use proportional shares T_i/2.

* When both reported totals are nonzero, use the preceding construction with cumulative values normalized as F_i/T_i for half marks and balance bits. At the final choice use the actual reported values to select the higher-valued side, including when T_i is negative. The interpolation witnesses for both possible bits apply after scaling by T_i.
* When exactly one total is zero, give all the cake to the positive-total agent if one exists, and otherwise give it to the zero-total agent. All receive at least their proportional share.
* When both totals are zero, use a benchmark allocation that gives the entire cake to agent 1. Both agents value this at zero. Ask each agent simultaneously for F_i(1/2), and propose the cut c given by the fractional part of the sum. Then ask both agents for F_i(c). If some orientation of the cut gives both agents nonnegative utility, choose such an orientation with fixed tie-breaking. Otherwise use the benchmark.

For nonzero totals, the proof of the final round and the best-case proof at the marks round are as before. At the marks round the earlier cloning argument can be replaced when the already published totals differ. For any reported mark m and full deviating type of i, take an opponent whose mark is strictly earlier than m. Its evaluation at m can now be chosen freely while preserving that earlier first half mark. On either side of the half-value threshold one can realize either balance bit. Therefore the adversary can make itself chooser and take i's better side at the reported cut. The deviator's worst case is at most T_i/2, and truth guarantees T_i/2.

In the zero-total subgame, the approval of a side at a fixed cut is a dominant truthful action. Each agent either gets the side she prefers or receives zero in the benchmark. If the other agent is indifferent and an agent strictly prefers a side, this is the unique mutually acceptable orientation. At the earlier proposal round, a truthful agent can obtain her preferred side at any interior c different from 1/2. Prescribe the opponent's value at 1/2 to yield that c, its value at c to favor the complementary side, and endpoints zero. Linear interpolation realizes the reports. Continuity handles excluded cut points for the supremum. Against a clone of her true valuation, no deviation can give more than zero because the opponent is guaranteed at least zero.

Finally, at the first, total-value query, a truthful agent of every type can attain the supremum over all endpoint pieces by encountering an opponent with the same total and the appropriate shape. Any deviation yields at most a proportional share against a clone of her true valuation, since the clone always receives at least its own proportional share. This checks every decision node even if an agent lies about the sign of its total.

[Direct-revelation results for all group sizes](cake-direct.md)

[Simultaneous batches for arbitrary group sizes](cake-batched.md) and [an explicit manipulation if the quantile rounds become public one by one](cake-public-rounds.md).
