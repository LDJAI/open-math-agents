# Can any prescribed shortlist be completed to a minimum dominating committee?

Manuel Lafond asked this question on August 5, 2014. In a tournament, each pair of candidates has a single winner. A committee dominates if every candidate outside it loses to at least one committee member. Write γ(T) for the minimum committee size, and f(k) for the fewest candidates in any tournament with γ(T)=k. Lafond asks whether there is an absolute constant c such that every prescribed group of k−c candidates extends to a minimum committee in every minimum-order tournament, allowing an eventual interpretation for large k. His specific intuition was that “it makes intuitive sense that it does for c = 1.” We found no published resolution. The listing awaits a Lean statement. [Left To Solve](https://lefttosolve.com/p/mo-177894) · [Original question](https://mathoverflow.net/questions/177894/properties-of-a-smallest-tournament-with-domination-number-k)

## Any two prescribed candidates can be included

**Theorem.** If T has minimum order among tournaments of domination number k, any two distinct vertices x and y belong to some minimum dominating set.

**Proof.** Merge x and y into a proxy z. Give z a win against another candidate v exactly when x or y beats v. An opponent who beats z therefore beats both x and y. Keep the other contests intact.

The smaller tournament has a dominating set D of size at most k−1. To see why, deleting a vertex can lower the domination number by at most one, since adding the vertex back to a dominating set always suffices. Any smaller tournament attaining a value above k would consequently contain a smaller tournament attaining k.

If D omits z, a member of D beats z and hence beats both x and y. The same D would dominate T, contradicting γ(T)=k. Thus D includes z. Replace z by x and y. The resulting set dominates T and has at most k members. Minimality forces its size to equal k. ∎

Consequently, if T has n candidates and k≥2, it has at least ⌈n(n−1)/(k(k−1))⌉ distinct minimum committees. Each candidate appears in at least ⌈(n−1)/(k−1)⌉ of them. Both bounds count prescribed pairs. The verified general theorem completes pairs for arbitrary k. For Lafond’s universal claim, the prescribed group itself must grow with k.

The Lean file also proves the one-vertex deletion result and that every edge of T lies on a directed triangle. To see the latter, take a minimum committee containing x and y with x beating y. On deleting y, some vertex w loses its committee cover. Since x covers y, w differs from y. Thus y beats w and w beats x. Related extremal results, including the nested-subtournament argument, predate this investigation. We make no priority claim for the pair theorem. [Reid, McRae, Hedetniemi and Hedetniemi, §3](https://ajc.maths.uq.edu.au/pdf/29/ajc_v29_p157.pdf)

## A four-candidate obstruction on 67 vertices

Use the Paley tournament on residues modulo 67. Candidate x beats y exactly when y−x is a nonzero quadratic residue. Consider the prescribed group U={0,1,2,5}. Its common beaters are W={13,32,43,46,53}. Every candidate, including each member of W, is strictly beaten by a member of W. Whichever fifth candidate joins U, some w in W still beats the whole committee. The committee therefore misses w.

The tournament does have domination number five. The committee {0,1,2,3,20} dominates, and exhaustive enumeration confirms no four-set dominates. Graham and Spencer had already recorded the latter property in 1971. Of the 766,480 possible four-sets, 69,278 have no one-candidate completion. These counts are supplementary to the explicit obstruction. [Graham and Spencer](https://doi.org/10.4153/CMB-1971-007-1)

This example is vertex-deletion critical. The group {22,59,60,62} dominates all vertices except 0. Translating these four labels supplies a certificate for each deleted vertex. Every prescribed pair nevertheless belongs to a minimum committee. Indeed the maps x↦ax+b, with a a nonzero square, act transitively on directed edges, so any pair in the displayed five-member committee may be mapped to any prescribed pair. Thus even deletion criticality and pair completion together leave room for failure at four prescribed vertices.

**Conditional implication.** If f(5)=67, the example disproves c=1 at k=5. Conversely, if c=1 works for all extremal tournaments at k=5, then f(5)≤66. The exact value of f(5) is unresolved. This argument leaves the eventual c=1 claim and the existence of a larger universal c open. [Reid et al., pp. 162, 166](https://ajc.maths.uq.edu.au/pdf/29/ajc_v29_p157.pdf)

## Verification

- `Tournament.lean` proves the prescribed-pair theorem using global order minimality, alongside the deletion and directed-triangle results.
- `PaleyCertificate.lean` proves that no single addition completes the specified four and verifies a dominating five-set.
- `python paley_completion.py` checks the exact domination number, the two explicit witness sets and the full distribution of completion counts. Translation symmetry reduces the enumeration to the 45,760 four-sets containing zero. Each total is recovered by counting its four choices of origin.
