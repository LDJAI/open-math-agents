import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar lemmas in the proof of the MAX-CUT norm reduction. The certificates
cover the coefficient ordering, arbitrary-dimensional graph encoding, and the
rank-one equality argument in terms of singular values. -/
namespace NormCutCertificate

/-- A descending spectrum encoding an edge-weight vector by consecutive gaps. -/
def spectrum : List ℤ → List ℤ
  | [] => []
  | a :: as => (a + as.sum) :: spectrum as

/-- A cut's objective evaluated on the gaps of a proposed spectrum. -/
def gapObjective : List ℤ → List ℤ → ℤ
  | c :: cs, s :: ss => c * (s - ss.headD 0) + gapObjective cs ss
  | _, _ => 0

/-- Ordinary dot product of a vector of cut indicators and a vector of edge weights. -/
def cutWeight : List ℤ → List ℤ → ℤ
  | c :: cs, a :: as => c * a + cutWeight cs as
  | _, _ => 0

theorem first_singular_value (as : List ℤ) : (spectrum as).headD 0 = as.sum := by
  cases as <;> simp [spectrum]

/-- The encoding preserves every cut weight, with no restriction on dimension,
number of vertices or sign of the integer edge weights. -/
theorem cut_encoding (cs as : List ℤ) : gapObjective cs (spectrum as) = cutWeight cs as := by
  induction cs generalizing as with
  | nil => simp [gapObjective,cutWeight]
  | cons c cs ih =>
    cases as with
    | nil => simp [spectrum,gapObjective,cutWeight]
    | cons a as =>
      change c * (a + as.sum - (spectrum as).headD 0) + gapObjective cs (spectrum as) = c * a + cutWeight cs as
      rw [first_singular_value, ih]
      ring

/-- Adjacent Ky Fan coefficients retain strictly descending weight even at
opposing cut-bit transitions. -/
theorem weight_gap {a b c : ℤ} (ha : a ≤ 1) (hb : 0 ≤ b) (hc : c ≤ 1)
    (B : ℤ) : 1 ≤ (B + 3 + b - a) - (B + c - b) := by omega

/-- Squared Frobenius norm is strictly below any weighted singular-value sum
with leading coefficient 1 and all remaining coefficients at least 1/2,
provided that the tail has positive total mass. -/
theorem strict_above_frobenius {ι : Type*} (I : Finset ι)
    (s w : ι → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hs : ∀ i ∈ I, 0 ≤ s i) (hbound : ∀ i ∈ I, s i ≤ x)
    (hw : ∀ i ∈ I, 1 / 2 ≤ w i) (hpos : 0 < ∑ i ∈ I, s i) :
    x^2 + ∑ i ∈ I, (s i)^2 < (x + ∑ i ∈ I, w i * s i)^2 := by
  have hsq : ∑ i ∈ I, (s i)^2 ≤ x * ∑ i ∈ I, s i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      nlinarith only [mul_nonneg (hs i hi) (sub_nonneg.mpr (hbound i hi))]
  have hlin : (1/2 : ℝ) * (∑ i ∈ I, s i) ≤ ∑ i ∈ I, w i * s i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hw i hi) (hs i hi)
  have hmid : x ^ 2 + ∑ i ∈ I, (s i)^2 < (x + (∑ i ∈ I, s i) / 2)^2 := by
    nlinarith only [hsq, mul_pos hpos hpos]
  have hmul := mul_nonneg (show 0 ≤ (∑ i ∈ I, w i * s i) - (∑ i ∈ I, s i)/2 by linarith only [hlin])
    (show 0 ≤ (x + ∑ i ∈ I, w i * s i) + (x + (∑ i ∈ I, s i)/2) by linarith only [hx,hpos,hlin])
  nlinarith only [hmid, hmul]

#print axioms cut_encoding
#print axioms weight_gap
#print axioms strict_above_frobenius
end NormCutCertificate
