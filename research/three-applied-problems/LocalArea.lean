import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
The local geometric and measure step for Tom Solberg's disk-bisection question.
Given a unit-Lipschitz linear height function and a point on the selected side
at depth h within distance D of the center, this proves the squared area bound.
The global depth estimate for shortest bisectors is a separate geometric argument.
-/
namespace SolbergLocal
open MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Homothetic contraction of the entire clipped disk into its selected half. -/
theorem local_area (C : Set Plane) (hC : Convex ℝ C) (p v : Plane)
    (hp : p ∈ C) (hv : v ∈ C) (ell : Plane →ₗ[ℝ] ℝ)
    (lip : ∀ a b : Plane, ell a - ell b ≤ dist a b)
    (s h D r : ℝ) (hpSide : s ≤ ell p) (hvDeep : s + h ≤ ell v)
    (hh : 0 < h) (hr : 0 < r) (hrD : r ≤ D) (hvp : dist v p ≤ D) :
    ENNReal.ofReal ((h / (D+h))^2) * volume (C ∩ Metric.closedBall p r) ≤
      volume ((C ∩ {y | s ≤ ell y}) ∩ Metric.closedBall p r) := by
  have hD : 0 < D := lt_of_lt_of_le hr hrD
  let a := r / D
  let k := h / (D+h)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one hD).2 hrD
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk1 : k ≤ 1 := (div_le_one (by positivity : 0 < D+h)).2 (by linarith)
  have haD : a*D = r := div_mul_cancel₀ r hD.ne'
  have hbalance : (1-k)*(a*h) = k*r := by
    dsimp [k,a]; field_simp; ring
  let c := AffineMap.lineMap p v a
  have hcC : c ∈ C := by
    rw [show c = (1-a) • p + a • v from AffineMap.lineMap_apply_module p v a]
    exact hC hp hv (sub_nonneg.mpr ha1) ha (by ring)
  have hcB : c ∈ Metric.closedBall p r := by
    rw [Metric.mem_closedBall, dist_eq_norm,
        show c = a • (v-p) + p from AffineMap.lineMap_apply_module' p v a,
        add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left hvp ha).trans haD.le
  have hcH : s + a*h ≤ ell c := by
    rw [show c = (1-a) • p + a • v from AffineMap.lineMap_apply_module p v a,
        map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hpSide (sub_nonneg.mpr ha1),
      mul_le_mul_of_nonneg_left hvDeep ha]
  have included : AffineMap.homothety c k '' (C ∩ Metric.closedBall p r) ⊆
      (C ∩ {y | s ≤ ell y}) ∩ Metric.closedBall p r := by
    rintro y ⟨x, ⟨hxC,hxB⟩, rfl⟩
    rw [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_module]
    have hxH : s-r ≤ ell x := by
      have hd : dist p x ≤ r := by simpa [dist_comm] using (Metric.mem_closedBall.mp hxB)
      linarith [lip p x]
    refine ⟨⟨hC hcC hxC (sub_nonneg.mpr hk1) hk (by ring), ?_⟩, ?_⟩
    · change s ≤ ell ((1-k) • c + k • x)
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hcH (sub_nonneg.mpr hk1),
        mul_le_mul_of_nonneg_left hxH hk]
    · exact (convex_closedBall p r) hcB hxB (sub_nonneg.mpr hk1) hk (by ring)
  have bound := measure_mono (μ := volume) included
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg k)] at bound
  exact bound

#print axioms SolbergLocal.local_area
end SolbergLocal
