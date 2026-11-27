# Do locally forced partnerships explain the lower tail?

The [Left To Solve entry](https://lefttosolve.com/p/LennonPittel.lennon_pittel_conjecture) asks if a uniformly random balanced market with complete independent strict preferences has at least εₙ E[Sₙ] stable matchings with probability tending to one for every positive nonincreasing εₙ tending to zero. Here Sₙ counts all stable complete matchings. Craig Lennon stated the conjecture in his [2007 thesis, §1.2 and (6.0.1)](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1194991095&disposition=inline). [Lennon and Pittel (2009)](https://doi.org/10.1017/S0963548308009607) imply a limiting lower bound of about 84.46% via their first two moments. The November 2026 catalog provides a Lean statement. A literature search found no proof of the limit one.

Multiple stable assignments give a market designer discretion while preserving stability. The conjecture describes that discretion under uniformly random preferences. The model need not represent preference distributions in particular clearinghouses.

## Conditioning on mutually first-ranked pairs

Let Xₙ count pairs who rank one another first. For an ordered list of r mutually disjoint pairs, the probability that all rank each other first is n⁻²ʳ. Rankings of the other agents are independent of this event. On deleting the specified agents and their counterparts from the other rankings, the remaining rankings are independently uniform.

Every stable matching must include each designated pair. Otherwise its members would block. Restricting stable matchings to the remaining agents is bijective, since an extension containing each designated pair creates no blocking pair incident to those agents. In particular, conditionally on the event for these *specified* pairs, Sₙ has exactly the distribution of Sₙ₋ᵣ. This argument does not condition on there being no further mutual first choices.

Write (x)ᵣ for the falling factorial. For any function f on nonnegative integers, counting ordered lists gives the exact identity

$$
\mathbb E[(X_n)_r f(S_n)]
=\frac{(n)_r^2}{n^{2r}}\,\mathbb E[f(S_{n-r})],\qquad 0\le r\le n,\ n\ge1.
$$

For j = 0, 1, 2, weight the profile probabilities proportionally to Sₙʲ. Under each of the three resulting laws, the rth factorial moment of Xₙ tends to one for each fixed r. Indeed, for j = 0 the moment ratio is one. For j = 1,2 the published asymptotics give E[Sₙ₋ᵣʲ]/E[Sₙʲ] → 1. The factorial moment method therefore gives the same Poisson(1) limit for Xₙ in all three laws. For each fixed integer k, the probability of Xₙ = k consequently tends to the same strictly positive constant. Dividing the weighted and unweighted probabilities shows

$$
\frac{\mathbb E[S_n^j\mid X_n=k]}{\mathbb E[S_n^j]}\longrightarrow 1,\qquad j=1,2.
$$

Thus for every fixed stratum Xₙ = k, conditioning leaves the limiting second-moment ratio unchanged. Applying a second-moment bound separately on these strata cannot improve its limiting success probability. The conjecture still requires control beyond these two moments.

## Testing larger independent submarkets

Call a pair of equally sized sets of agents isolated if each of its members places every opposite-side member of the pair of sets above every outsider. In any stable matching, these two sets match internally. Otherwise some man and some woman from the sets would each be assigned outside, and they would block. Stable matchings of this block and its complement therefore combine freely. Every cross-block candidate pair contains a block member who prefers their assigned partner.

Let Zₖ count these blocks of size k on each side. Each of the 2k agents must have a specified set of top k choices, giving

$$
\mathbb E Z_k=\binom nk^{2-2k}.
$$

For k = 2, this is asymptotic to 4/n⁴. Two different size-two blocks can coexist only if their male sets and their female sets are each disjoint. If one agent overlapped, its top two choices would force the other side to coincide, which would force the first side to coincide too. For disjoint blocks the events are independent, so E[(Z₂)₂] ≤ (E Z₂)². Bonferroni gives Pr(Z₂ ≥ 1) ∼ E Z₂.

For 3 ≤ k ≤ n−2, summing expectations is at most a geometric series starting at binom(n,2)⁻⁴, since binom(n,k) ≥ binom(n,2). For k = n−1 the expectation is n^(4−2n). It follows that the probability of any proper isolated block of size at least two is asymptotic to **4/n⁴**. Hence such blocks cannot account for a positive-probability lower tail under this model. Blocks requiring weaker preference separation remain possible.

## Verification and remaining gap

ForcedPair.lean defines stability using the same strict blocking-pair comparisons as the catalog, with generic agent labels and natural-valued ranks. Its theorem deleteMutualFirst is the deterministic bijection for one pair. The mixed-moment identity and the asymptotic calculations above are paper arguments. We have no lower-tail theorem for the remaining market. No complete proof of the listed conjecture is asserted.

The independent script check_exact.py verified the finite mixed-moment identity by exhaustive enumeration of all 1, 16, and 46,656 profiles for n = 1, 2, and 3, for every r ≤ n and j = 0, 1, 2. It uses integer counts and rational arithmetic.

Lean 4.33.1 checked ForcedPair.deleteMutualFirst. The axiom audit reported propext, Classical.choice, and Quot.sound.
