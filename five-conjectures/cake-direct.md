# Proportionality under direct revelation for any number of agents

**Scope.** Agents simultaneously report their entire valuations. This proves an all-population result in the direct-revelation model and answers a related question from §6.2 at this level. It leaves the finite Robertson–Webb question in §7.2 open. Ortega and Segal-Halevi distinguish the two models and already give direct-revelation monotonicity-of-the-extremes lemmas for nonnegative valuations and unrestricted Pareto efficiency. This note uses efficiency relative to a specified class of connected allocations and permits signed valuations in the proportional result. [Original paper, §§3, 6.2 and 7.2](https://doi.org/10.1007/s00355-022-01416-4)

## Two observations

Fix any number of agents at least two. A valuation is a finite nonatomic additive signed measure with total utility 1. A connected allocation partitions the full unit interval into one interval per agent. In a direct mechanism, obvious manipulation means raising either the best possible utility or the worst possible utility over all opponent reports.

* **Worst case.** Every proportional rule, whatever its other properties, protects an honest agent's worst-case utility at 1/n or better. Fix a deviating report and make all opponents truthful copies of the agent's actual valuation. Each opponent has to receive at least 1/n under that valuation. Additivity then leaves the deviator at most 1/n. This is the clone argument of Ortega and Segal-Halevi.
* **Best case.** Fix a proposed partition with agent i assigned interval J. Give each opponent a valuation maximized on its assigned interval. If this benchmark partition satisfies the rule's eligibility requirements on the resulting truthful profile, it Pareto-dominates every feasible allocation that gives i strictly less than u_i(J). Therefore any rule selecting an allocation which is Pareto efficient within its eligible set gives i at least u_i(J) on that profile.

For the second observation, a normalized uniform density supported on each opponent's designated positive-length interval suffices. If the domain demands genuinely signed types, let the density be negative on the complement and a positive constant on the designated interval, chosen to make the total value 1. This makes the designated interval a global maximizer of utility.

## Theorem 1. Connected proportional division of a mixed cake

Every direct rule that selects a Pareto-efficient member of the connected proportional allocations is NOM. Such a rule exists for every finite number of agents.

**Existence.** Starting with a remaining interval and m participants, have each mark its first prefix worth 1/m of its positive remaining value. Give the shortest prefix to its marker. By continuity, all others value that prefix at no more than their threshold. By induction each participant keeping cake after this step values the remainder at least (m−1)/n. The marker obtains at least 1/n. This establishes nonemptiness of the set of connected proportional allocations even for signed valuations. It does not assert anything about manipulation of the procedure.

For each left-to-right order of recipients, the cut coordinates form a compact simplex. Continuity of cumulative valuations makes the proportionality constraints closed. Over the finite union of such feasible sets maximize the sum of the reported utilities and use a fixed tie breaker. The selected allocation is Pareto efficient within this set.

**Best-case proof.** Let U be the supremum of agent i's value over all pieces she can receive in a connected partition with n positive-length intervals. Any piece achievable by a deviation in this rule belongs to this class, since a zero-length interval cannot be worth 1/n to its recipient. The supremum U is at least 1 by shrinking all other pieces to an endpoint and using continuity. Choose a partition with u_i(J) arbitrarily near U and above 1/n. Give the other agents the valuations in the second observation. The benchmark is proportional for all. The selected truthful allocation gives i at least u_i(J), so the truthful supremum is U. Apply the worst-case observation to finish.

## Theorem 2. Connected envy-free division of a nonnegative cake

For every finite n there is a direct-revelation NOM rule which returns an envy-free, connected division of a nonnegative cake. This supplies an affirmative answer in the direct model to the connected envy-free question in §6.2 of Ortega and Segal-Halevi. The 2020 paper asks it separately from the mixed-cake conjecture.

Choose a welfare-maximizing member of the connected envy-free allocations. Such allocations exist by Stromquist's connected envy-free existence theorem. The domain with weakly positive densities or arbitrary nonatomic nonnegative measures follows by adding a small everywhere-positive uniform component, then passing to a convergent subsequence of cut coordinates with fixed order of recipients. Compactness and closedness again guarantee a maximizer for the reported measures. Envy-freeness implies proportionality, so the worst-case argument applies.

For the best case, take J to be the long suffix [δ,1]. Choose δ so small that agent i values the prefix at less than 1/2. Partition the prefix into n−1 positive-length intervals and have each other agent place its entire value on its designated interval. The resulting benchmark is envy-free: each other agent gets its maximum 1 and values every other piece at zero, while i strictly prefers the suffix to each prefix piece. Any connected envy-free allocation giving i less than u_i(J) is Pareto dominated by the benchmark. The selected allocation therefore gives i at least u_i(J). Because u_i(J) tends to 1, truthful play achieves supremum 1, the largest possible outcome for any report.

These arguments need no assumptions on how the welfare objective breaks ties. The cited paper's direct-revelation theorem allows disconnected pieces and uses global Pareto efficiency. The present conclusion addresses connectedness by using only comparisons to benchmark allocations that themselves satisfy the requisite connectedness and fairness conditions. Direct preference reports are essential to the proof as given. Stromquist also proves that finite query protocols cannot always produce an exact connected envy-free allocation for at least three players.

[Stromquist, How to Cut a Cake Fairly (1980)](https://www.eecs.harvard.edu/cs286r/courses/fall11/papers/Stromquist80.pdf) · [Stromquist, Envy-free cake divisions cannot be found by finite protocols (2008)](https://www.cs.umd.edu/users/gasarch/TOPICS/cake/lbenvyfree.pdf)
