# Two prime powers in the length-five gap

For a length-five witness write the lower block as n+1 through n+5 and the upper block as n+d+1 through n+d+5. Suppose its upper product equals 25 times the lower product, and d is at least five. For every factorization

$$d=p^e q^f t$$

with prime bases and nonnegative exponents, the proofs give

$$t>10^{33},\qquad d<10^{92}t^{10},\qquad n<2d.$$

In particular, the gap must have at least three distinct prime divisors. The two bases may coincide. Taking each exponent to be its full exponent in the gap shows that the restriction survives removal of the two largest prime-power factors. The general existence question still allows gaps with a large third cofactor.

## The divisibility from the two blocks

Set C = 7,962,624 = 576² × 24, and let Eᵢ = 24(n+1+i) − d for 0 ≤ i < 5. For every prime power h dividing the gap there is an i such that h² divides CEᵢ. To see this, d divides 24 times the lower product. That product divides 24 times the LCM of the five entries. Consequently h divides 576 times this LCM. If r is the largest divisor of h dividing the LCM, h divides 576r, and r divides an entry n+1+i. The matching upper entry is congruent to it modulo r. Expanding the two products modulo r² gives r² dividing i!(4−i)!Eᵢ. The factorial coefficient divides 24. This proves the assertion, including for the prime bases 2, 3, and 5.

Apply it to the two specified prime powers separately. This gives indices i,j with

$$\frac{E_iE_j}{d^2}=\frac{u}{C^2t^2}$$

for an integer u. This step multiplies two divisibilities, so it also works if the primes or the indices coincide.

## Excluding all small cofactors

Write α for the positive fifth root of 25. The fifth power of the smallest ratio of corresponding entries is at most 25, and the fifth power of the greatest is at least 25. In particular, n+1 ≤ d/(α−1) ≤ n+5. Each CEᵢ/d therefore lies very close to the same real number C(24/(α−1)−1). The prior proof that n exceeds a one followed by 160 zeros makes that interval narrow enough to use a determinant-one pair of fractions.

The new Lean module checks exact integer bounds on the fifth powers, the product interval, and the two adjacent fractions surrounding it. Their denominators sum to more than a one followed by 66 zeros. Every strictly intermediate fraction, including an unreduced one, has denominator at least that sum. The fraction with numerator u and denominator t² lies strictly inside. Hence t exceeds one decillion, a one followed by 33 zeros. The large rational certificate constants are in FiveGap.lean. Decimal arithmetic played no role in checking them.

## Bounding the gap for every cofactor

Define the integral homogeneous quintic

$$G(X,Y)=X^5-500X^4Y-100250X^3Y^2-1562500X^2Y^3+1332190625XY^4-165567610000Y^5.$$

It has no zero in nonnegative integers with Y positive. Modulo 11 its only zero is the pair (0,0), as Lean checks on the 121 residue pairs. Homogeneity would then give a smaller solution by dividing both coordinates by 11.

At any witness, the polynomial G(EᵢEⱼ,d²) has absolute value at most (2 × 10²²)d⁹. The degree-ten terms cancel against a polynomial multiple of the original product equation. The fifteen coefficient lists, one per unordered index pair, give exact identities checked by Lean. For the remaining monomials use n < 2d and d ≥ 1. The file gen_effective.py reproduces those lists using SymPy.

Put V = C²t². The relation VEᵢEⱼ = d²u and homogeneity give

$$d^{10}G(u,V)=V^5 G(E_iE_j,d^2).$$

The integer on the left after removing d¹⁰ is nonzero. Taking absolute values and cancelling d⁹ yields d ≤ (2 × 10²²)C¹⁰t¹⁰ < 10⁹²t¹⁰. Thus each *fixed* cofactor gives a finite search over both block starts and both prime-power factors. This last proof is independent of the earlier bounded search.

## Verification

The updated archive includes the original dependencies. From its root, run `bash verify.sh PATH_TO_BUILT_MATHLIB`. Use Lean 4.33.1 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. For the new results the last four modules are FiveGap, FiveEffective, FiveCertificates and FiveFinite. The audit is in logs/five-gap-lean.log.
