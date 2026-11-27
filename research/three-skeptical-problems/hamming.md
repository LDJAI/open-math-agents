# The expected closest overlapping binary window

On April 25, 2013, MathOverflow user32786 asked for the expected minimum Hamming distance between a uniform binary word and the first k overlapping windows of an independent fair binary sequence. Anthony Quas commented, “I doubt that you can give an explicit function. However, I think you can get a very good approximation.” He suggested a binomial approximation. His 1993 mathematics PhD is documented by the University of Warwick. The author welcomed bounds as well. The public MathOverflow post has zero answers. Its Math Stack Exchange cross-post currently returns 404 and the Stack Exchange API returns no public question or answers there. The final limit in the source has k tending to zero. Its context and the almost-sure occurrence of every fixed word give the intended limit as k tends to infinity.

[MathOverflow question and comment](https://mathoverflow.net/questions/128755/expected-minimum-hamming-distance-with-overlaps) · [University of Warwick dissertation](https://wrap.warwick.ac.uk/id/eprint/58569/)

## Exact result

Let the pattern bits be independent fair bits A₀,…,Aₙ₋₁, and let the text B be a separate independent fair sequence. For distinct nonnegative shifts i in a finite nonempty set S, write Dᵢ for the number of mismatches between A and the word starting at Bᵢ. Construct a bipartite graph with vertices Aₜ and Bₛ and one edge (Aₜ,Bₜ₊ᵢ) for each pattern position t and shift i. Let Eᵢ be the edges for shift i. Here k=|S|, and the original question uses S={0,…,k−1}.

For any subset H of the edges that gives even degree at every vertex, set hᵢ=|H∩Eᵢ|. For 1 ≤ r ≤ n put

$$
C_r(0)=\sum_{d=r}^{n}\binom nd,\qquad
C_r(h)=-\sum_{j=0}^{r-1}(-1)^j\binom{h-1}{j}\binom{n-h}{r-1-j}\quad(1\le h\le n).
$$

Binomial coefficients with lower index outside the usual range equal zero. Then

$$
\mathbb E\min_{i\in S}D_i
=2^{-nk}\sum_{r=1}^{n}\ \sum_{H\text{ even}}\ \prod_{i\in S}C_r(h_i).
$$

The inner sum divided by 2ⁿᵏ is the exact probability that every chosen window has at least r mismatches. The quantities C are binomial tails at zero and signed Krawtchouk coefficients at positive h. The summands depend only on the incidence of cycles among the overlapping windows. There are 2^(e−v+c) even edge sets, where e, v and c denote the edge, vertex and component counts.

## Proof

For an edge e=(u,v) in Eᵢ the generating function factor is

$$
z_i^{u\mathbin{\mathrm{xor}}v} = \tfrac12\big((1+z_i)+(1-z_i)(-1)^{u+v}\big).
$$

Multiply all factors and take expectations over independent fair vertex labels. Each term is indexed by the edges H on which the second term was chosen. The sign has mean zero whenever some vertex occurs an odd number of times. For even H the sign is identically one. The full joint probability generating function is consequently

$$
P(\boldsymbol z)=2^{-nk}\sum_{H\text{ even}}\prod_{i\in S}(1+z_i)^{n-h_i}(1-z_i)^{h_i}.
$$

This character calculation is the usual even-subgraph expansion, equivalently the split weight-enumerator transform for a binary graphic cut code. Summing coefficients with all exponents at least r factorizes within each term. At h>0 the sum of all coefficients of (1+z)ⁿ⁻ʰ(1−z)ʰ is zero, so its coefficient tail is the negative of the coefficient of zʳ⁻¹ in (1+z)ⁿ⁻ʰ(1−z)ʰ⁻¹. For h=0 one obtains the ordinary binomial tail. Sum the joint tail probabilities over r.

## Which shifts give independent distances?

The selected distances are mutually independent if and only if their graph is a forest. In a forest only the empty even subgraph contributes, so the generating function factorizes into k ordinary binomial generating functions. Conversely, the event that all distances vanish forces all the labels within each connected component to coincide. Its probability equals 2^(c−v). Under independence it would be 2^(−e), since each window comprises n independent bit comparisons. Equality holds precisely when e=v−c.

Any two distinct shifts form a forest. A walk alternating between the two shifts changes the pattern index by their nonzero difference every two steps and cannot close without backtracking. For at least three consecutive shifts and n≥2, the four edges between A₀,A₁ and B₁,B₂ give a cycle. Thus pairwise independence survives all overlaps while joint independence already fails. The biconditional applies to arbitrary shift sets, including nonconsecutive ones.

## Finite computation for fixed number of windows

With S={0,…,k−1}, process the pattern in successive rows. Initialize the suffix of k−1 text bits uniformly. At each row append one new text bit b, sample one new pattern bit a, and compare a to each of the k bits in the resulting block. Add these k indicators to the cumulative distance vector. Drop the oldest text bit. The complete joint law after n rows is exact because the algorithm has generated each of the independent input bits once.

Rows with complementary suffixes can be grouped, keeping the same distance vector. Complementing all the bits of a suffix, its next text bit and the next pattern bit preserves the row increments and complements the next suffix. At k≥2 there are 2^(k−2) suffix representatives, and at k=1 there is one. Each state has four equally likely transitions, with at most two distinct next suffix classes. After row t there are at most (t+1)^k distance vectors. Computing all n rows therefore costs O(k 2^max(0,k−2) (n+1)^(k+1)) elementary integer operations and O(2^max(0,k−2) (n+1)^k) integer table entries. This is polynomial in n for fixed k. Integer counters require O(n+k) bits. The implementation checks against full enumeration.

For n=2,k=3 the exact mean is 7/16. Three independent binomial counts would give 7/16 as well, despite different tails, so the mean alone can conceal dependence. For the overlapping windows the tails at r=1,2 are 13/32,1/32, while independent windows have tails 27/64,1/64. At n=3,k=4 the formula gives 21/32. The independently sampled minimum would instead be ((7/8)^4+(1/2)^4+(1/8)^4)=1329/2048, distinct from 21/32.

## Prior work and what can be claimed

Atallah, Jacquet and Szpankowski (1993) studied the maximum match score for random text and pattern, using cyclic text indexing. Their Theorem 9 gives a finite bivariate generating function, and Lemma 5 already established pairwise independence for a symmetric alphabet. Their main result concerns the asymptotic maximum. Their article does not furnish the general finite joint law for all selected shifts or the arbitrary-shift forest criterion presented here. [Published article](https://doi.org/10.1002/rsa.3240040206) · [Full text, section 3.4](https://www.academia.edu/161860/A_probabilistic_analysis_of_a_pattern_matching_problem)

Régnier and Szpankowski gave an exact analysis of approximate occurrences of a specified pattern in a random text in a 1996 report published in 1997. Navarro’s 2001 survey explicitly discusses the difficulty of averaging the result over patterns. An exact finite method already follows from conditioning on all 2ⁿ patterns, and direct enumeration is also possible. The novel-status question concerns the pattern-free, arbitrary-shift cycle formula and associated characterization. This search located no earlier presentation of that specialized result, and does not establish priority. The MathOverflow post is an explicit-formula question and a skeptic’s comment, not a community consensus or formally stated impossibility conjecture. [Purdue technical report](https://docs.lib.purdue.edu/cstech/1337/) · [Navarro survey](https://doi.org/10.1145/375360.375365)

The included standard-library Python program independently compares the full transfer distribution and all cycle-formula tails against exhaustive sampling over all words for 20 choices with 1≤n≤4 and 1≤k≤5. It also compares the forest criterion with the full joint law for 90 arbitrary shift sets and lengths. These computations supplement the proofs.
