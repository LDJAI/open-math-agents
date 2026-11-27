# A local Gaussian field with the prescribed square covariance

Abdelmalek Abdesselam asked in April 2015 whether a local, centered, finite-variance function of a fractional Gaussian field can have twice the square of its covariance away from coincident points. The question addresses the supercritical regime, in which the usual construction of a Wick square faces a divergence. On April 22, 2015, Martin Hairer wrote, “Regarding a possible no-go theorem, I suspect that it is indeed the case”. Hairer is a mathematics professor and 2014 Fields Medalist. He received his PhD in physics at the University of Geneva in 2001. Abdesselam himself cited neighboring results pointing in both directions. The original post had no public answers on inspection. [Original question and discussion](https://mathoverflow.net/questions/201997/squaring-random-schwartz-distributions) · [Hairer’s CV](https://www.hairer.org/cv.pdf) · [Institute for Advanced Study](https://www.ias.edu/scholars/martin-hairer)

## Result

Write h for the scaling dimension and assume d/4 < h < d/2. A real scalar constant-coefficient differential operator applied to the field satisfies all the stated conditions **if and only if**

$$
h=2m,\quad m\in\mathbb Z_{>0},\qquad 4m<d<8m,\qquad d\equiv1\pmod4 .
$$

Every such operator is a scalar multiple of the m-th power of the Laplacian. Its magnitude is determined by the covariance normalization. This gives infinitely many supercritical examples, beginning with d=5 and h=2, and rules out a blanket no-go theorem for the posted covariance and locality requirements.

These maps belong to the first Gaussian chaos and are odd in the field. The usual centered Wick square belongs to the second chaos and is even. The post specifies no parity condition, chaos order, mixed correlation with the input, or convergence from a regularized square. In fact the first-chaos theorem below proves that every centered, even, local finite-variance output is zero almost surely throughout the stated supercritical range. Thus a genuine nonzero even square is impossible under these hypotheses. Existence at all other parameters for arbitrary spatially varying first-chaos operators remains a separate question. The weaker integrability alternative in the original post is also outside this theorem.

## Construction

For the stated range of h, the covariance away from the origin has the form C(z)=γ|z|⁻²ʰ, where γ>0. The spectral density is |ξ|²ʰ⁻ᵈ in the normalization used in the question. For a>0 and z≠0 write

$$
K_j(a)=\prod_{t=0}^{j-1}(a+2t)(a+2t+2-d),\qquad
\Delta^j |z|^{-a}=K_j(a)|z|^{-a-2j}.
$$

This follows by differentiating a radial function and iterating. Set h=2m and write r=d−4m. If 4m<d<8m and d≡1 mod 4, then r≡1 mod 4 and 0<r<4m. In K₂ₘ(4m) all the first factors are positive. The second factors are 2(t+1)−r. None is zero, and exactly (r−1)/2 are negative, an even number. Thus K₂ₘ(4m)>0. Define

$$
Sq(\phi)=s_m\Delta^m\phi,\qquad s_m=\sqrt{2\gamma/K_{2m}(4m)}.
$$

The operator is a continuous linear map on tempered distributions. For any Schwartz test f, its evaluation is sₘφ(Δᵐf), a centered Gaussian with finite variance. If f is supported in U then so is Δᵐf, which proves the required measurability with respect to the field in U. Differentiation in both covariance variables gives, off the diagonal,

$$
s_m^2\Delta_x^m\Delta_y^m C(x-y)
=s_m^2\gamma K_{2m}(4m)|x-y|^{-8m}
=2C(x-y)^2.
$$

Differentiating the original covariance as a distribution supplies the extension across the diagonal. For instance, in d=5 the two radial factors multiply to 4·18=72, so Sq(φ)=(√γ/6)Δφ.

## Necessity and uniqueness within constant-coefficient scalar differential operators

Let P(D) be a candidate with real coefficients, and write p(ξ)=P(iξ). Denote by ℓ and L the lowest and highest degrees present in p. The covariance multiplier of the output is |p(ξ)|²|ξ|²ʰ⁻ᵈ. Average the squared symbol over rotations. It becomes a polynomial ∑ⱼqⱼ|ξ|²ʲ, with nonzero endpoints qℓ,qL>0. In fact they are the spherical averages of the squared magnitudes of the corresponding homogeneous parts. The requested output covariance is already rotationally invariant away from the origin. Consequently its rotational average has that same restriction:

$$
2\gamma^2 |z|^{-4h}
=\gamma\sum_j q_j(-1)^jK_j(2h)|z|^{-2h-2j},\qquad z\ne0.
$$

If Kℓ(2h)=0, then every term on the right vanishes. Otherwise the slowest-decaying nonzero power has j=ℓ. Equality of powers forces ℓ=h, in particular h is an integer. In even dimension the factor at t+1=(d−2h)/2 in Kₕ(2h) vanishes, since 0<(d−2h)/2<h. Thus d must be odd. In odd dimension none of the factors Kⱼ(2h) vanish for integral h. The nonzero top coefficient now forces L=ℓ=h, so p is homogeneous.

It remains to show that the original, unaveraged operator is rotationally invariant up to the normalization. For each rotation R the two output covariances associated with p(Rξ) and p(ξ) agree off the origin. Their difference is supported at the origin. The Fourier transform of a distribution supported at one point is a polynomial. On the line ξ=tu, |u|=1, t≠0, that polynomial must equal

$$
\bigl(|p(Ru)|^2-|p(u)|^2\bigr)|t|^{4h-d}.
$$

This uses homogeneity and the spectral density. Equality of the Fourier multipliers away from the origin holds pointwise there by continuity. The exponent 4h−d is a positive odd integer. No nonzero constant multiple of |t| raised to an odd power agrees with a polynomial on both half-lines. Hence |p| is constant on the sphere. Homogeneity and real coefficients give p=iʰp₀ with p₀ real and homogeneous. The continuous real p₀ has constant nonzero magnitude on the connected unit sphere here (h positive integral gives d>2). It is therefore constant there. Its parity forces h even and its homogeneous extension is a multiple of |ξ|ʰ. Thus P(D) is a multiple of Δᵐ, where h=2m.

Finally let r=d−4m. The covariance coefficient is a positive square times K₂ₘ(4m). For odd d, its sign is (−1)^((r−1)/2). Positivity requires d≡1 mod 4. This proves the claimed classification, including normalization up to sign.


## Why a genuine even square is impossible

**First-chaos theorem.** Throughout d/4<h<d/2, let Y be any random tempered distribution given by a measurable local map of the input field, and suppose each Y(f) is centered and has finite variance. For every Schwartz test f, Y(f) lies in the first Wiener chaos of the input field. This conclusion requires no translation covariance of the map. If the map is even in the input field, its output vanishes almost surely as a random tempered distribution.

**Proof.** Put s=d/2−h, so 0<s<d/4. Let H be the completion of the real Schwartz functions under the input covariance norm
$$
\|g\|_H^2=\int |\widehat g(\xi)|^2|\xi|^{-2s}\,d\xi .
$$
The centered random variables φ(g) form the corresponding isonormal Gaussian family. For an open U let H(U) be the closure of tests supported in U. The Wiener–Itô expansion of an L² random variable measurable with respect to this subfamily has its k-th kernel in the symmetric tensor power H(U)^{⊙k}. This follows by expanding in Hermite polynomials of an orthonormal basis of H(U), extended to one of H. The closure is unchanged if the underlying σ-algebras are completed.

Write Kₖ(f) for the k-th chaos kernel of Y(f). Each depends linearly on the **test** f, because each realized output is a distribution and chaos projection is linear. The Fourier norm on H^{⊗k} has weight ∏ⱼ|ξⱼ|⁻²ˢ. Since
$$
 (1+\textstyle\sum_j |\xi_j|^2)^{-ks}\ \leq\ \prod_j|\xi_j|^{-2s},
$$
inverse Fourier transformation embeds H^{⊗k} continuously and injectively into the usual Sobolev distribution space H^{−ks} on R^{kd}. In this spatial realization tensors from H(U)^{⊗k} are supported in the product of k copies of the closure of U. Indeed they are norm limits of sums of elementary tensor products with that support, and convergence in the Sobolev space implies distributional convergence.

Fix a compactly supported smooth f. If supp f⊂U, locality puts Kₖ(f) in H(U)^{⊙k}. For any ε>0 a finite smooth partition of unity writes f as the sum of tests supported in balls of diameter less than ε. Thus the support of Kₖ(f) is contained in the closed set where every two of the k coordinates are at distance at most ε. Taking arbitrarily small ε forces the kernel to be supported on the total diagonal.

For clarity, a distribution in H^{−r} supported on a linear subspace of codimension D is zero whenever 2r<D. In orthogonal tangent and normal coordinates (u,v), multiply any fixed compactly supported smooth test ψ(u,v) by a smooth cutoff χ(v/ε) equal to one near v=0. Its pairing with the distribution is unchanged. The cutoff test has L² norm O(ε^{D/2}) and Hᴹ norm O(ε^{D/2−M}) for any positive integer M, by differentiating and estimating the tube volume. Sobolev interpolation with M≥r bounds its Hʳ norm by O(ε^{D/2−r}), which tends to zero. Duality proves the assertion.

For k≥2 the diagonal has codimension D=d(k−1), and 2ks<kd/2≤d(k−1). Hence Kₖ(f)=0 for all k≥2. The zeroth chaos vanishes by centering. This proves the result for compactly supported smooth tests.

Finally f↦Y(f) is a linear map from the Schwartz space to L² with closed graph. If fⱼ converges to f in Schwartz space and Y(fⱼ) converges to Z in L², passage to an almost surely convergent subsequence and samplewise continuity of the output distributions imply Z=Y(f). The closed-graph theorem and density of compactly supported tests now extend the conclusion to all Schwartz tests. A first-chaos variable changes sign under φ↦−φ almost surely. If Y is even it must also retain its sign, so Y(f)=0 almost surely for each f. Using a countable dense set of tests and samplewise continuity makes this simultaneous and proves Y=0 almost surely.

Dobrushin and Kel'bert had already identified the diagonal-support mechanism for local set-additive functionals of Gaussian generalized fields in Proposition 2 of their 1979 note. Their Proposition 5 rules out nonlinear, stationarily related, set-additive functionals of the massive free Markov field in dimensions greater than four. Their subsequent papers develop this theory. The proof above uses the smooth-test formulation in the question and a short Sobolev argument for the full specified massless fractional family, without stationarity of the output. [1979 paper](https://www.mathnet.ru/links/8405ecfb704b0da88ca37fbd33f77ccb/rm4129_eng.pdf) · [Local additive functionals](https://doi.org/10.1137/1128002) · [Stationary local additive functionals](https://doi.org/10.1137/1128048)

## Classification under translation equivariance

Suppose additionally that the operation commutes with spatial translations on the input and output, as an equality of random fields for each translation. This condition concerns their joint coupling. Translation invariance of the output covariance alone does not impose it. Then the existence criterion above classifies **all** measurable, centered, finite-variance local operations, without a linearity or differential-operator assumption.

Indeed, by the first-chaos theorem there is a unique deterministic linear map T from tests to H with Y(f)=φ(Tf) in L². The closed-graph argument and the Gaussian isometry make T continuous. For compactly supported f, its first kernel Tf is supported in supp f, by localization in every open neighborhood. The Gaussian isometry and the translation-equivariance assumption imply T commutes with translations. Viewed as a map from Schwartz tests to tempered distributions, such a continuous operator is convolution with a tempered distribution. To see the support constraint directly, its Schwartz kernel in the two spatial variables is translation invariant along the diagonal and, by localization, supported on the diagonal. In difference and base-point coordinates it is a distribution in the difference variable times Lebesgue measure in the base point, with difference support at zero. The point-supported factor is a finite linear combination of derivatives of the delta distribution. Thus T, and its transpose on field samples, is a real scalar constant-coefficient differential operator. The preceding classification applies. Equality at all tests holds almost surely simultaneously by separability and distributional continuity.

## Status and prior work

The source for the fractional Gaussian field itself already gives its covariance formulas and the behavior of such fields under fractional powers of the Laplacian. Those classical facts supply the construction. Abdesselam’s later work treats products made by mollification and renormalization. His 2021 edit cites that work for h<d/4. Hairer’s 2025 follow-up comments concern a genuine Wick square in the four-dimensional critical case. These are different requirements from the supercritical covariance-only assertion addressed here. Searches of the question title, the later paper and the fractional-Gaussian-field literature found no earlier answer giving this constant-coefficient classification. This is a bounded literature search, not a priority guarantee. [Lodhia, Sheffield, Sun and Watson, Fractional Gaussian fields: a survey](https://arxiv.org/abs/1407.5598) · [Abdesselam, A Second-Quantized Kolmogorov–Chentsov Theorem via the Operator Product Expansion](https://arxiv.org/abs/1604.05259) · [Left to Solve entry](https://lefttosolve.com/p/mo-201997)
