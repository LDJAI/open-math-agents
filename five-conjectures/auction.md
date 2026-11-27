# A local truthful auction for private unit-demand lists and values

Hassidim, Mansour and Vardi's 2013 preprint asks in §10, Question 2, whether a truthful local mechanism exists when both the acceptable-item sets and the valuations are private. The authors write, “We conjecture that this is impossible”. In the model of §7.2, each buyer assigns *one common private value* to all the items in her acceptable set, whose size is at most a fixed constant $k$. The question states no approximation threshold. We prove a deterministic, worst-case fraction $1/k$ of the maximum welfare. This applies to arbitrary reported demand graphs of bounded item degree. The random-list assumption in the original paper ensures that degree bound with high probability.

**Prior art.** The price rule is mechanism M1, Figure 1 of Devanur, Hartline, Karlin and Nguyen (WINE 2011), where it is used to analyze revenue. The observations below specialize that rule, resolve ties, bound its worst-case welfare, and establish locality in the later question. The rule predates the question. The literature search found no paper explicitly deriving this locality and welfare corollary for Question 2. Priority for either corollary remains unverified.

## Mechanism

Buyer $i$ has type $(S_i,v_i)$, where $|S_i|\le k$ and $v_i\ge0$. Her value is $v_i$ for an item in $S_i$ and zero for other items. Each item has one copy and a buyer takes at most one. Utilities are value minus payment. Reports have the same format as types, and zero-value reports may be treated as empty lists.

1. On every item with claimants, select the highest bidder provisionally. Resolve equal bids by a fixed public order of buyers.
2. The price to provisional winner $i$ on item $j$ is the largest bid of any other claimant on $j$, or zero if none exists.
3. Each provisional winner keeps one of the items she provisionally wins, choosing the one with the lowest price. Break item ties by a fixed public order, and charge the stated price. A winner may be assigned an item even when its price equals her value. The remaining items stay unsold. Other buyers pay zero.

All provisional decisions use the same original reports. Dropping an item in step 3 does not change its price or ownership in step 1.

## Theorem and proof

The mechanism is feasible, individually rational, dominant-strategy truthful for joint reports of lists and values, and obtains at least $1/k$ of optimal social welfare.

**Feasibility and incentives.** An item can be kept only by its unique provisional winner. Hold all reports except $i$'s fixed. For each possible item, let $p_j$ be the largest competing bid on that item, taking the maximum of an empty list to be zero. A truthful report attains utility

$$
 U_i=\max\bigl(\{0\}\cup\{v_i-p_j:j\in S_i\}\bigr).
$$

Indeed every strictly profitable option is won provisionally under the truthful report, and choosing the cheapest provisional item maximizes true utility. Ties lost at the boundary $p_j=v_i$ have zero surplus and leave this equality intact. A lie that obtains a truly acceptable item $j$ still pays exactly $p_j$. A lie that obtains an unacceptable item yields nonpositive utility. Thus no misreport improves upon $U_i$, which is nonnegative.

**Welfare.** Fix an optimal matching and discard zero-value edges. Charge the value of each matched item to its provisional winner. The winner's value is at least the optimal matched buyer's value for this item. A provisional winner keeps a truly acceptable item, so the mechanism obtains her full value once. She can be charged for at most $k$ distinct items. Summation gives $\mathrm{OPT}\le k\,\mathrm{ALG}$.

**Sharpness for this mechanism.** Give a first-priority buyer value one on all $k$ items. Give each item another buyer who wants only that item at value one. The first buyer provisionally wins every item and keeps one, giving welfare one. The optimal welfare is $k$. All item degrees are two. For strict bids replace the first buyer's value by $1+\varepsilon$, giving welfare ratio tending to $1/k$.

## Local implementation and input access

Assume random access to both sides of the *reported* incidence graph, so one can enumerate the buyers who listed an item and the items listed by a buyer. Each bid occupies one word, or comparison time is accounted for separately. This is the standard graph-probe interface described in Vardi's thesis. If the only input is a flat list of buyer submissions, building the reverse index is a preprocessing cost.

Write $D$ for maximum reported item degree. A buyer query scans at most $k$ lists, each of length at most $D$. It takes $O(k(D+1))$ word operations. Keeping the two best bids with priorities in one scan suffices. An item query first finds its provisional winner and then recomputes that single buyer's final choice, with the same asymptotic bound. Answers are independent of query order. If the paper's buyers independently choose uniformly random lists of length at most $k$, with $kn/m$ bounded, $D=O(\log(n+1))$ with high probability. For example, conditional on a given buyer listing an item, the number of other buyers listing it is a sum of independent Bernoulli variables with bounded mean. A Chernoff bound followed by a union bound over at most $kn$ listed incidences proves the claim.

**Optional hard cap.** To guarantee a fixed running time on arbitrary reports, suppress each item with more than a chosen cutoff $D_0$ reports, detecting this by reading at most $D_0+1$ neighbors. An item can be obtained by $i$ precisely when fewer than $D_0$ rivals listed it and her report wins the bid comparison. The extra eligibility condition is independent of her own report, so the same incentive proof applies on all profiles. The welfare benchmark restricted to unsuppressed items remains valid on every profile. It equals the unrestricted benchmark whenever the maximum degree is at most $D_0$.

## Different private values for different items

Here is a randomized extension on the broader domain with at most $k$ positive values per buyer. Independently keep each item with probability $p$, then apply M1 on retained items. Each provisional winner chooses the item maximizing value minus price, with opting out worth zero and ties with opting out resolved in favor of taking a won item. Truthfulness holds for every realization of the retained set, by the same menu proof with $v_{ij}$ replacing $v_i$. The original deterministic rule's uniform-value welfare proof uses the equality of a buyer's positive values and does not apply directly to this domain.

Fix an optimal matching. For each positively valued item $j$ in that matching, let $h(j)$ be its highest-value bidder before sampling, with the same fixed priority. Whenever $j$ survives and all other positive-value items of $h(j)$ do not, she takes $j$ with value at least the optimum's value on this item. The event has probability at least $p(1-p)^{k-1}$. Linearity of expectation over distinct optimal items gives this same fraction of optimal welfare on *every fixed valuation profile*. For $k>1$ take $p=1/k$, which gives at least $1/(ek)$. For $k=1$ keep all items. Only $k$-wise independence is used. With $p$ replaced by the dyadic number $2^{-\lceil\log_2 k\rceil}$, this gives at least $1/(2ek)$ and allows a short public seed. For example, evaluate a random polynomial of degree $k-1$ at distinct item labels in a binary field of size at least $max(m,2^{\lceil\log_2 k\rceil})$ and retain an item if its first $\lceil\log_2 k\rceil$ output bits vanish. For fixed $k$, this is polylogarithmic in the item universe size. The usual public random tape formulation also suffices. The optional hard cap applies unchanged.

## Sources and verification

- Hassidim, Mansour and Vardi, *Local Computation Mechanism Design*, preprint first posted in 2013, §§7.1, 7.2, 10. [Paper](https://arxiv.org/pdf/1311.3939)
- Devanur, Hartline, Karlin and Nguyen, *Prior-independent Multi-Parameter Mechanism Design*, WINE 2011, §3.1, Figure 1. [Paper](https://eecs.northwestern.edu/~hartline/papers/auctions-WINE-11.pdf)
- Shai Vardi, *Design and Analysis of Local Computation Algorithms*, §2, graph probes, and §10, local auctions. [Thesis](https://www.cs.tau.ac.il/~mansour/students/Vardi_Shai-PhD.pdf)

The Lean 4.33.1 file `LocalAuction.lean` proves the incentive and welfare arguments for arbitrary finite sizes and real values. `truthful_menu` defines the provisional eligibility test and chooses a cheapest provisional item. It proves that truthful utility dominates the utility of every alternative at the fixed rival prices. `welfare_bound` proves the counting inequality for any finite comparison matching under the stated highest-bid and incidence hypotheses. `welfare_of_choices` connects the counting inequality to the realized welfare of the actual minimum-price choices. The formal file takes the rivals' prices, tie priority flags and item champions as inputs. The identification of those inputs with the auction, the graph access bound, and the item-sampling extension are justified in the written proof.

The accompanying Python script independently enumerates feasible allocations and profitable deviations on small finite domains. Run `python3 verify_auction.py` in this directory. The all-size results follow from the proofs above.
