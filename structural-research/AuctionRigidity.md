# Can a truthful full-supply auction beat Vickrey revenue at every profile?

**Result.** For any n > k ≥ 1, a deterministic, dominant-strategy truthful, ex-post individually rational auction of k identical units to n unit-demand bidders must allocate to the top k at every profile of pairwise distinct bids if it always sells k units and its revenue is at least the k-unit Vickrey revenue at every profile. This includes exceptional profiles of probability zero under continuous bid distributions. The proof uses only finite averages, makes no regularity assumption on the mechanism, and allows subsidies. Bids and valuations range over all nonnegative reals; utility is the allocated value minus the payment.

Jack posed the question on October 29, 2010, explicitly using v₁ > ··· > vₙ. Dave Pritchard's January 2011 answer gives a truthful counterexample if ties are included. It gives two equal low bidders both goods even when a third bidder bids strictly more. Pritchard then conjectures top-two efficiency on every distinct profile. The other answer assumes equal winner payments; the original author points out why this need not follow from truthfulness. Our theorem handles the unresolved distinct-bid question for arbitrary n and k. Ex-post participation is the standard assumption explicitly invoked in the answers. Without it the answer is trivially negative: always assign goods to predetermined bidders and charge each such bidder the maximum of the other bids. These charges are independent of own reports and dominate the benchmark, but can exceed the winner's value. [Question and responses](https://mathoverflow.net/questions/44164/truthful-multi-unit-auctions-that-guarantee-selling-all-items) · [Left To Solve](https://lefttosolve.com/p/mo-44164)

## 1. Payment normalization

Write xᵢ ∈ {0,1} for the actual winner indicators and yᵢ for those of Vickrey, with a fixed consistent tie priority. Fix all rivals' bids. DSIC implies xᵢ is nondecreasing in the remaining bid, by adding the incentive inequalities in opposite directions. Within each of its two outcome classes the payment is constant. If both classes occur, writing their payments as p₀ and p₁ shows that every losing bid is ≤ p₁−p₀ and every winning bid is ≥ p₁−p₀. Thus the rule is a threshold, including an arbitrary endpoint convention. IR implies p₀ ≤ 0. Normalizing to zero when losing and to the threshold when winning weakly increases each payment. If the bidder always loses, normalize to zero; if the bidder always wins, her constant payment is at most zero by individual rationality at type zero and again can be normalized to zero. Hence we may work with the normalized revenue-dominating rule and finite or infinite thresholds. Vickrey's threshold at fixed rivals is their kth highest bid, denoted tᵢ.

## 2. An exact finite-grid virtual-value estimate

Fix any B > 0. Draw a free bid uniformly from h,2h,…,Nh with h=B/N, and define φ(b)=2b−B. For fixed rivals the winning grid bids are a suffix. If the first winner is Jh then its threshold τ lies in [(J−1)h,Jh], including the case J=1. The conditional average of φ over this suffix is exactly Jh because the endpoint bids are Jh and B. Consequently

$$
0\leq \mathbb E[\phi(b_i)x_i-p_i]\leq h.
$$

For an empty suffix both sides vanish. The same estimate holds for Vickrey. Moreover the fraction D of positions at which two threshold rules disagree satisfies

$$
|\min(B,\tau)-t_i|\ \leq\ BD+2h
$$

when all rivals are in [0,B]. Indeed the number of losing positions divided by N times B approximates each clipped threshold within h. The two losing sets are nested grid prefixes, and the difference of their counts is exactly ND.

## 3. From random-profile optimality to pointwise rigidity

Choose an arbitrary profile of distinct nonnegative target bids and B larger than their maximum. Prove the following for every subset S of bidders. Hold their bids fixed at the corresponding target bids and draw each free bid independently from the same finite mesh. Then the probability that x differs from y tends to zero as N→∞. All expectations and comparisons below concern finite sets. The conclusion for S consisting of all bidders gives the theorem, since that profile no longer varies.

Assume the assertion holds for every face with one fewer fixed coordinate. For each i in S, use the result for S without i. On that face average first along the i-th grid line. The expected fraction D of i-specific allocation disagreements tends to zero. The grid threshold estimate therefore implies

$$
\mathbb E|\min(B,\tau_i)-t_i|\longrightarrow0
$$

over the other free coordinates. Setting i to its fixed target aᵢ now gives the correct winner decision with probability tending to one. To check this, unless aᵢ is within δ of the Vickrey threshold or the two clipped thresholds differ by at least δ, the decisions coincide (take δ < B−aᵢ). The latter event tends to zero by Markov's inequality. The former requires some rival bid to lie within δ of aᵢ. With just one bidder fixed there are no fixed rivals. Otherwise the distinct target bids have a positive minimum separation, so no fixed rival can do so for sufficiently small δ, and each free rival has probability at most 2δ/B+2/N. Send N to infinity and then δ to zero. With coinciding decisions, normalized payments either both vanish or differ by at most the threshold difference; with decisions differing both payments lie in [0,B]. Hence the expected absolute difference of the fixed bidder's payments also tends to zero. This argument applies to every i in S, using its own smaller face. At S empty, these conclusions hold vacuously.

Let W = Σᵢ bᵢ(yᵢ−xᵢ) ≥ 0 be the pointwise loss in efficient surplus. Because both rules allocate exactly k items, Σᵢ φ(bᵢ)(xᵢ−yᵢ) = −2W. Compare expected revenue. On free coordinates replace revenue by virtual surplus at error at most h per rule per bidder. The fixed-coordinate expected differences in both payments and virtual surplus tend to zero, as proved above. Pointwise revenue dominance therefore implies 2 E W ≤ o(1)+2nh, so E W→0. It even suffices to assume revenue dominance only on distinct profiles: ties occur with probability O(1/N) on each face and normalized revenues lie in [0,kB].

Whenever all bids are separated pairwise by at least δ and the two allocations differ, W ≥ δ, since at least one strictly higher bidder was displaced. The probability of any near-tie between a free coordinate and another free or fixed coordinate is at most binom(n,2)(2δ/B+2/N). The fixed bids are themselves distinct. Markov's inequality for W, followed by δ↓0, gives the desired convergence. This completes the induction.

## Status and limits

The tie counterexample remains valid. The theorem concerns deterministic winner sets. Truthful-in-expectation randomized mechanisms allow fractional interim allocations and require a different proof. The argument uses the full report domain, ex-post participation, and an ex-post revenue guarantee as stated above. The October 2010 post and its two responses were checked in full, along with searches for fixed-supply revenue dominance, Vickrey/VCG uniqueness, and the exact question title. We found no prior proof of the strict-profile assertion. Myerson’s expected-revenue comparison alone yields almost-everywhere efficiency under a continuous prior. The face argument is needed to rule out isolated exceptional profiles. The standard starting point is [Myerson's payment characterization](https://doi.org/10.1287/moor.6.1.58). The proof above includes the needed elementary special case.

## Pointwise check when exceptional profiles matter

Börgers, Li and Wang prove ex-post revenue undominance for a single object sold by a second-price auction with a deterministic reserve, including zero reserve (Theorem 3 of their July 2025 paper). Their theorem compares revenue vectors and admits randomized rules. Our result identifies the deterministic allocation at each distinct profile for arbitrary fixed supply. [Undominated Mechanisms](https://public.websites.umich.edu/~tborgers/Undominated.pdf)

For the single-unit case with distinct bids, there is also a short direct argument. If the winner differs from the highest bidder, the revenue guarantee and participation force the winner to have the second-highest bid and to pay that entire bid. Raise only that winner's bid to a value strictly between the original second and first bids. DSIC leaves her a winner and keeps her payment constant. Every other bidder is a loser and pays at most zero. The guaranteed second-price revenue has strictly increased, which is impossible. The face proof above deals with arbitrary supply, where other winners' payments could also change under a unilateral report.

## Lean verification

The full theorem is formalized as `AuctionModel.strict_profile_theorem : AuctionQuestion.DistinctProfileRigidity` in `AuctionResult.lean`. The proof includes DSIC and participation normalization, Vickrey critical prices, finite mesh estimates, product resampling, pairwise anti-concentration, welfare loss, induction over all frozen subsets, and return to the original unrestricted type space. Its axiom audit lists `propext`, `Classical.choice`, and `Quot.sound`. The stronger hand observation about a revenue guarantee imposed only at distinct profiles is outside this formal statement.

The pointwise guarantee and the conclusion have different quantifiers. The Lean theorem assumes the revenue guarantee at every admissible profile, including ties. It concludes efficiency at every admissible profile with distinct bids. It allows any finite n and k with 0 < k < n, negative payments consistent with ex-post participation, and arbitrary behavior at threshold endpoints. There are no assumptions of continuity, measurability, anonymity, symmetry, or equal payments across winners.
