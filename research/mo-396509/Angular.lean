import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The one-dimensional inequality for Pinelis's averaging conjecture

`angular_bound` proves the integrated inequality for every admissible angular gauge.
`symmetric_gauge_bound` derives the angular hypotheses from permutation symmetry and convexity.
`ordered_gap_identities` and `radial_identity` check the two changes of integrand.
This file has no dependence on the formal conjecture or on its statement placeholder.
-/

namespace PinelisAveraging

open Set MeasureTheory

private def lin (A B t : ℝ) : ℝ := (1 - t) * A + t * B
private def weight (t : ℝ) : ℝ := 9 * |2 * t - 1| - 5

private lemma lin_pos {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < lin A B t := by
  rcases ht with ⟨h0, h1⟩
  by_cases h : t = 0
  · simp [h, lin, hA]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr h1) hA.le)
      (mul_pos (lt_of_le_of_ne h0 (Ne.symm h)) hB)

private lemma continuous_lin (A B : ℝ) : Continuous (lin A B) := by
  unfold lin
  fun_prop

private lemma continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

private lemma quotient_integrable {u v : ℝ} {num den : ℝ → ℝ} (huv : u ≤ v)
    (hn : ContinuousOn num (Icc u v)) (hd : ContinuousOn den (Icc u v))
    (hp : ∀ t ∈ Icc u v, 0 < den t) :
    IntervalIntegrable (fun t => num t / den t ^ 3) volume u v :=
  ContinuousOn.intervalIntegrable_of_Icc huv (hn.div (hd.pow 3) (fun t ht => pow_ne_zero 3 (hp t ht).ne'))

private noncomputable def primitive (A B C D t : ℝ) : ℝ :=
  (D / (2 * A)) * (t / lin A B t) ^ 2 - (C / (2 * B)) * ((1 - t) / lin A B t) ^ 2

private lemma primitive_deriv {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (C D t : ℝ)
    (ht : 0 < lin A B t) :
    HasDerivAt (primitive A B C D) (lin C D t / lin A B t ^ 3) t := by
  have hOne := hasDerivAt_const t (1 : ℝ)
  have hId := hasDerivAt_id t
  have hLeft : HasDerivAt (fun s : ℝ => 1 - s) (0 - 1) t := hOne.sub hId
  have hDen : HasDerivAt (lin A B) ((0 - 1) * A + 1 * B) t :=
    (hLeft.mul_const A).add (hId.mul_const B)
  have h1 := ((hId.div hDen ht.ne').pow 2).const_mul (D / (2 * A))
  have h2 := ((hLeft.div hDen ht.ne').pow 2).const_mul (C / (2 * B))
  apply (h1.sub h2).congr_deriv
  simp only [Pi.div_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hA.ne', hB.ne', ht.ne']
  unfold lin
  ring

private lemma line_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ t in (0 : ℝ)..1, weight t / lin A B t ^ 3) =
      ((B - 2 * A) * (2 * B - A)) / (A ^ 2 * B ^ 2 * (A + B)) := by
  have evalPart (u v C D : ℝ) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v)
      (ident : ∀ t ∈ Icc u v, weight t = lin C D t) :
      (∫ t in u..v, weight t / lin A B t ^ 3) =
        primitive A B C D v - primitive A B C D u := by
    have hp (t : ℝ) (ht : t ∈ Icc u v) : 0 < lin A B t :=
      lin_pos hA hB ⟨hu.trans ht.1, ht.2.trans hv⟩
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le huv] at ht
      rw [ident t ht]
      exact primitive_deriv hA hB C D t (hp t ht)
    · exact quotient_integrable huv continuous_weight.continuousOn (continuous_lin A B).continuousOn hp
  have hl := evalPart 0 (1 / 2) 4 (-14) (by norm_num) (by norm_num) (by norm_num) (by
    intro t ht
    simp only [weight, lin, abs_of_nonpos (show 2*t-1 ≤ 0 by linarith [ht.2])]
    ring)
  have hr := evalPart (1 / 2) 1 (-14) 4 (by norm_num) (by norm_num) (by norm_num) (by
    intro t ht
    simp only [weight, lin, abs_of_nonneg (show 0 ≤ 2*t-1 by linarith [ht.1])]
    ring)
  have integ (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v) :=
    quotient_integrable huv continuous_weight.continuousOn (continuous_lin A B).continuousOn
      (fun t (ht : t ∈ Icc u v) => lin_pos hA hB ⟨hu.trans ht.1, ht.2.trans hv⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals (integ 0 (1/2) (by norm_num) (by norm_num) (by norm_num))
    (integ (1/2) 1 (by norm_num) (by norm_num) (by norm_num)), hl, hr]
  have hsum : A + B ≠ 0 := (add_pos hA hB).ne'
  simp only [primitive, lin, sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring_nf
  field_simp [hA.ne', hB.ne', hsum]
  ring_nf

/-- The one-dimensional form of the sharp inequality. The last two hypotheses
are the two inequalities supplied by swapping pairs of coordinates on a slice. -/
theorem angular_bound (q : ℝ → ℝ) (hc : ContinuousOn q (Icc 0 1))
    (hconv : ConvexOn ℝ (Icc 0 1) q) (hp : ∀ t ∈ Icc 0 1, 0 < q t)
    (hLeft : 11 * q (2/9) ≤ 16 * q (7/9)) (hRight : 11 * q (7/9) ≤ 16 * q (2/9)) :
    (∫ t in (0 : ℝ)..1, (9 * |2*t-1| - 5) / q t ^ 3) ≤ 0 := by
  let A := (7 * q (2/9) - 2 * q (7/9)) / 5
  let B := (7 * q (7/9) - 2 * q (2/9)) / 5
  have ma : (2/9 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have mb : (7/9 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hA : 0 < A := by dsimp [A]; linarith [hp _ ma]
  have hB : 0 < B := by dsimp [B]; linarith [hp _ mb]
  have hAB : B ≤ 2*A := by dsimp [A,B]; linarith
  have hBA : A ≤ 2*B := by dsimp [A,B]; linarith
  have fitA : q (2/9) = lin A B (2/9) := by dsimp [lin,A,B]; ring
  have fitB : q (7/9) = lin A B (7/9) := by dsimp [lin,A,B]; ring
  have compare (t : ℝ) (ht : t ∈ Icc 0 1) :
      weight t / q t ^ 3 ≤ weight t / lin A B t ^ 3 := by
    have hqt := hp t ht
    have hlt := lin_pos hA hB ht
    apply (div_le_div_iff₀ (pow_pos hqt 3) (pow_pos hlt 3)).2
    have outside (hq : lin A B t ≤ q t) (hw : 0 ≤ weight t) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlt.le hq 3) hw
    rcases lt_trichotomy t (2/9) with h | h | h
    · apply outside
      · have s := hconv.secant_mono_aux1 ht mb h (show (2/9:ℝ) < 7/9 by norm_num)
        rw [fitA,fitB] at s
        unfold lin at s ⊢
        nlinarith only [s]
      · rw [weight, abs_of_nonpos (show 2*t-1 ≤ 0 by linarith)]
        linarith
    · subst t; rw [fitA]
    · rcases lt_trichotomy t (7/9) with k | k | k
      · have s := hconv.secant_mono_aux1 ma mb h k
        rw [fitA,fitB] at s
        have hq : q t ≤ lin A B t := by unfold lin at s ⊢; nlinarith only [s]
        have hw : weight t ≤ 0 := by
          by_cases ht' : 2*t-1 ≤ 0
          · rw [weight, abs_of_nonpos ht']; linarith
          · rw [weight, abs_of_nonneg (le_of_not_ge ht')]; linarith
        exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hqt.le hq 3) hw
      · subst t; rw [fitB]
      · apply outside
        · have s := hconv.secant_mono_aux1 ma ht (show (2/9:ℝ) < 7/9 by norm_num) k
          rw [fitA,fitB] at s
          unfold lin at s ⊢
          nlinarith only [s]
        · rw [weight, abs_of_nonneg (show 0 ≤ 2*t-1 by linarith)]
          linarith
  change (∫ t in (0 : ℝ)..1, weight t / q t ^ 3) ≤ 0
  calc
    _ ≤ (∫ t in (0 : ℝ)..1, weight t / lin A B t ^ 3) :=
      intervalIntegral.integral_mono_on zero_le_one
        (quotient_integrable zero_le_one continuous_weight.continuousOn hc hp)
        (quotient_integrable zero_le_one continuous_weight.continuousOn
          (continuous_lin A B).continuousOn (fun _ ht => lin_pos hA hB ht)) compare
    _ = _ := line_integral hA hB
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hAB) (sub_nonneg.mpr hBA)) (by positivity)

/-- A centered ordered triple of range one, parametrized by its first gap fraction. -/
noncomputable def ray (t : ℝ) : ℝ × ℝ × ℝ := ((-1-t)/3, (2*t-1)/3, (2-t)/3)

private def swapFirst (v : ℝ × ℝ × ℝ) := (v.2.1, v.1, v.2.2)
private def swapLast (v : ℝ × ℝ × ℝ) := (v.1, v.2.2, v.2.1)

/-- A continuous convex positively homogeneous function, invariant under the adjacent
swaps and positive on the ordered rays, satisfies the sharp angular integral bound.
The hypotheses only use vectors in the centered plane, except for the domain of `p`.
For example the planar gauge extends to triples by first subtracting their mean. -/
theorem symmetric_gauge_bound (p : ℝ × ℝ × ℝ → ℝ) (hc : Continuous p)
    (hconv : ConvexOn ℝ univ p) (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < p (ray t))
    (hom : ∀ (r : ℝ), 0 ≤ r → ∀ v, p (r • v) = r * p v)
    (first : ∀ x y z, p (y,x,z) = p (x,y,z))
    (last : ∀ x y z, p (x,z,y) = p (x,y,z)) :
    (∫ t in (0 : ℝ)..1, (9 * |2*t-1| - 5) / (p (ray t)) ^ 3) ≤ 0 := by
  apply angular_bound (fun t => p (ray t))
  · exact (hc.comp (show Continuous ray by unfold ray; fun_prop)).continuousOn
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro x _ y _ a b ha hb hab
    have hr : ray (a • x + b • y) = a • ray x + b • ray y := by
      ext <;> simp [ray, smul_eq_mul] <;> linarith only [hab]
    change p (ray (a • x + b • y)) ≤ _
    rw [hr]
    exact hconv.2 (mem_univ _) (mem_univ _) ha hb hab
  · exact hpos
  · have idL : (11/16 : ℝ) • ray (2/9) =
          (67/112 : ℝ) • ray (7/9) + (45/112 : ℝ) • swapFirst (ray (7/9)) := by
      ext <;> norm_num [ray,swapFirst]
    have h := hconv.2 (mem_univ (ray (7/9))) (mem_univ (swapFirst (ray (7/9))))
      (show 0 ≤ (67/112:ℝ) by norm_num) (show 0 ≤ (45/112:ℝ) by norm_num) (by norm_num)
    rw [← idL, hom _ (by norm_num), show p (swapFirst (ray (7/9))) = p (ray (7/9)) from first _ _ _] at h
    simp only [smul_eq_mul] at h
    linarith only [h]
  · have idR : (11/16 : ℝ) • ray (7/9) =
          (67/112 : ℝ) • ray (2/9) + (45/112 : ℝ) • swapLast (ray (2/9)) := by
      ext <;> norm_num [ray,swapLast]
    have h := hconv.2 (mem_univ (ray (2/9))) (mem_univ (swapLast (ray (2/9))))
      (show 0 ≤ (67/112:ℝ) by norm_num) (show 0 ≤ (45/112:ℝ) by norm_num) (by norm_num)
    rw [← idR, hom _ (by norm_num), show p (swapLast (ray (2/9))) = p (ray (2/9)) from last _ _ _] at h
    simp only [smul_eq_mul] at h
    linarith only [h]

/-- Averages over the three choices of a target among ordered observations. -/
theorem ordered_gap_identities {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (|b-a| + |c-b| + |c-a|) / 3 = 2*(c-a)/3 ∧
    (|(b+c)/2-a| + |(a+c)/2-b| + |(a+b)/2-c|) / 3 =
      (3*(c-a) + |(b-a)-(c-b)|)/6 := by
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (sub_nonneg.mpr hbc),
      abs_of_nonneg (sub_nonneg.mpr (hab.trans hbc))]
    ring
  · rw [abs_of_nonneg (show 0 ≤ (b+c)/2-a by linarith),
      abs_of_nonpos (show (a+b)/2-c ≤ 0 by linarith),
      show (a+c)/2-b = -((b-a)-(c-b))/2 by ring, abs_div, abs_neg]
    norm_num
    ring

/-- Integrating the signed gap inequality radially supplies the cubic weight in
`angular_bound`. The factor `s` in the integrand is the area Jacobian. -/
theorem radial_identity (q : ℝ → ℝ) (hq : ∀ t ∈ Icc (0 : ℝ) 1, 0 < q t) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1/q t,
        (9 * |s*t - s*(1-t)| - 5*(s*t + s*(1-t))) * s) =
      (1/3 : ℝ) * ∫ t in (0 : ℝ)..1, (9 * |2*t-1| - 5) / q t ^ 3 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have pos := hq t ht
  have hn : (0 : ℝ) ≤ 1/q t := by positivity
  calc
    _ = (∫ s in (0 : ℝ)..1/q t, (9*|2*t-1|-5)*s^2) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hn] at hs
      dsimp only
      rw [show s*t-s*(1-t) = s*(2*t-1) by ring, abs_mul, abs_of_nonneg hs.1]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring

end PinelisAveraging

#print axioms PinelisAveraging.angular_bound
#print axioms PinelisAveraging.symmetric_gauge_bound
#print axioms PinelisAveraging.ordered_gap_identities
#print axioms PinelisAveraging.radial_identity
