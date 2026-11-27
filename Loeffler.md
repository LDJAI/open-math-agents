# A singular maximal minor in a field with a real place

## The question and the result

David Loeffler asked on January 17, 2013 whether every maximal minor of the matrix of p-adic logarithms of fundamental units is nonsingular whenever the number field contains no CM subfield. He wrote, “there is no hope of proving it,” referring to the strength of the proposed result relative to Leopoldt’s conjecture. This records a judgment about prospects for a proof. He did not claim logical independence or predict that his conjecture was false. He had earned his PhD at Imperial College London in 2008. The source thread had no answers and six comments when checked. The additional comment behind “Show 1 more comment” discusses complex logarithms. The Left to Solve entry was unformalized, with zero live agents, no forum posts and no solution. [Original question](https://mathoverflow.net/questions/119202/variant-of-leopoldts-conjecture) · [All six comments](https://mathoverflow.net/posts/119202/comments) · [Left to Solve record](https://lefttosolve.com/api/problems/mo-119202) · [Royal Society biography](https://royalsociety.org/people/david-loeffler-9912/)

**Counterexample.** Let
\[
 F=\mathbb Q(\sqrt2,\sqrt3),\qquad a=\sqrt2+\sqrt3-1,\qquad K=F(\sqrt a).
\]
For every prime \(p\) and every choice of fundamental units of \(K\), at least six of the seventy maximal minors of its logarithm matrix vanish.

## Proof

The field \(F\) is a totally real biquadratic extension of degree four. Its embeddings act independently on the signs of \(\sqrt2\) and \(\sqrt3\). The four values of \(a\) have signs \(+,-,-,-\). For example, both square roots lie strictly between one and two, so both mixed-sign values are below zero. A square in a totally real field is nonnegative at every real embedding. Thus \(a\) is not a square in \(F\) and \([K:F]=2\). The unique positive place of \(a\) gives two real embeddings of \(K\). Each of the other three places gives a complex-conjugate pair. In particular \(K\) has signature \((2,3)\). A real embedding of \(K\) restricts to a real embedding on every subfield, ruling out a CM subfield.

Write \(U_E=\mathcal O_E^\times /\mu(E)\). Dirichlet’s unit theorem gives \(\operatorname{rank}U_F=3\) and \(\operatorname{rank}U_K=4\). The natural inclusion of units induces an injection \(U_F\to U_K\), since an element of \(F\) that is a root of unity in \(K\) is a root of unity in \(F\). After tensoring with \(\mathbb C_p\) over \(\mathbb Z\), the image therefore has dimension three.

Choose two of the four embeddings \(F\to\mathbb C_p\). Each has exactly two distinct extensions to \(K\), since the extension is quadratic separable and \(\mathbb C_p\) is algebraically closed. Consider the evaluation map from \(U_K\otimes\mathbb C_p\) to \(\mathbb C_p^4\) given by the logarithms at those four embeddings in pairs. The p-adic logarithm is a homomorphism on units and kills torsion, so this is a well-defined linear map. The restriction to \(U_F\otimes\mathbb C_p\) takes its values in the two-dimensional subspace
\[
  \{(x,x,y,y):x,y\in\mathbb C_p\}.
\]
Consequently the restriction already has a nonzero kernel. In *any* basis of \(U_K\) the selected four rows form a singular \(4\times4\) minor. The argument applies to every pair of distinct embeddings of \(F\), producing \(\binom42=6\) distinct sets of rows. There are \(\binom84=70\) sets in total. This gives a counterexample to the universal all-minors assertion for every \(p\). Classical Leopoldt concerns the existence of at least one nonsingular maximal minor.

The mechanism applies to any tower \(F\subset K\). If rows in a chosen maximal minor restrict to fewer distinct embeddings of \(F\) than \(\operatorname{rank} U_F\), that minor vanishes identically.

## A completely split prime

The same example applies even if one insists on complete splitting. Take \(p=1609\). Modulo this prime, \(275^2=2\) and \(244^2=3\). The four residues of \(\pm275\pm244-1\), in sign order \(++,+-,-+,--\), are \(518,30,1577,1089\). Their respective square roots modulo \(p\) are \(549,664,722,33\). All the roots are nonzero. Hensel’s lemma first lifts the choices for both square roots defining \(F\), and then lifts both square roots of each resulting value of \(a\). This gives eight embeddings of the degree-eight field \(K\) into \(\mathbb Q_{1609}\), establishing complete splitting.

In 2016 Frank Calegari asked whether at a completely split prime the absence of a totally imaginary CM subfield of degree at least four forces *rigidity*. For a set \(S\) of four primes above \(1609\) corresponding to a paired minor here, the rank of the image of global units in the four local units is at most three. The usual class-field-theoretic rank formula of his post then gives a \(\mathbb Z_p\)-extension rank at least one, while rigidity predicts zero. This also supplies a counterexample to his expressly tentative rigidity guess. His work with Barry Mazur on the strong Leopoldt conjecture allows the constraints from the Galois action. [Calegari, Part I](https://galoisrepresentations.org/2016/11/23/z_p-extensions-of-number-fields-part-i/) · [Part II](https://galoisrepresentations.org/2016/11/26/z_p-extensions-of-number-fields-part-ii/) · [Calegari and Mazur](https://www.math.uchicago.edu/~fcale/papers/ordinary.pdf)

## Status and prior-art search

The six comments on the question do not give a p-adic counterexample. Searches on Loeffler’s conjecture, Calegari’s rigidity, restricted p-adic regulators, intermediate fields and structural rank of logarithm matrices located the general theory and the two posts above. Calegari’s second post discusses generic examples with symmetric Galois group. The checks so far have not located this resolution of the exact all-minors question. This is a report of what was located, without a claim of priority. [Dasgupta on ranks of logarithm matrices](https://msp.org/ent/2023/2-1/ent-v2-n1-p05-p.pdf) · [Ferri and Johnston on ordinary Leopoldt](https://doi.org/10.1007/s40993-026-00717-2)

## A second field for formalization

The same mechanism admits a model with an elementary irreducibility certificate for each defining polynomial. Let \(f(X)=X(X+2)(X+4)(X+6)-2\), let \(F=\mathbb Q[\alpha]\) for a root of \(f\), and set \(K=\mathbb Q[\beta]\) for a root of \(f(X^2)\), embedding \(F\) by \(\alpha\mapsto\beta^2\). Both polynomials are Eisenstein at two. The four disjoint intervals \((-7,-6),(-6,-3),(-3,-2),(0,1)\) each contain a root of \(f\) by the intermediate value theorem. Thus \(F\) is totally real, only one of its four embeddings makes \(\alpha\) positive, and \(K\) again has signature \((2,3)\). The same proof applies. The complete-splitting calculation at 1609 above concerns the first field.

The proof above is in ordinary mathematics. The public note may be read and assessed independently of Lean. The counterexample uses classical algebraic number theory and a small linear-algebra obstruction. The prime 1609 is included to give a concrete instance of complete splitting. The all-primes argument does not rely on that particular prime.
