import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Sion
import Mathlib.Tactic

/-!
# Verified components of the Lyapunov trace formula

Ludwig's 2018 question: https://mathoverflow.net/q/309804.
The accompanying mathematical proof is at
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/769.

This file verifies the trace identity, the spectral upper bound, the dual
spectral obstruction, the minimax step, and the conversion of a spectral
cap into a lower bound. The analytic Gramian construction and the assembly
of these components into the supremum theorem are in the research note.
-/

open Matrix Set
open scoped BigOperators Matrix

namespace LyapunovTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev M (ι : Type*) := Matrix ι ι ℝ

theorem trace_identity {A P X : M ι} (hP : P.PosDef)
    (h : A * P + P * A.transpose = -X) :
    (X * P⁻¹).trace = -2 * A.trace := by
  have hu := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hx : X = -(A * P + P * A.transpose) := by rw [h, neg_neg]
  rw [hx, neg_mul, add_mul, Matrix.trace_neg, Matrix.trace_add,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu,
    Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hu, one_mul, Matrix.trace_transpose]
  ring

omit [DecidableEq ι] in
/-- The scalar inequality used after diagonalizing the Gramian. -/
theorem weighted_bound (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 < u i)
    (h1 : ∑ i, w i = 1) {t : ℝ} (ht : 0 < t) (hmean : ∑ i, w i * u i = t)
    {s : ℝ} (hs : 0 < s) :
    ∑ i, w i * (u i / (1 + s * u i)) ≤ t / (1 + s * t) := by
  have denom : 0 < (1 + s * t)^2 := by positivity
  calc
    ∑ i, w i * (u i / (1 + s * u i))
      ≤ ∑ i, w i * ((s*t^2 + u i) / (1+s*t)^2) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        apply (div_le_div_iff₀ (by have := hu i; positivity) denom).2
        nlinarith [mul_nonneg hs.le (sq_nonneg (u i - t))]
    _ = t / (1 + s*t) := by
        simp_rw [← mul_div_assoc, mul_add]
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul, hmean]
        field_simp
        ring

/-- Minimax turns a bound witnessed separately against each opponent into a single design. -/
theorem minimax_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Set E} {K : Set F} (dne : D.Nonempty) (dc : Convex ℝ D) (dk : IsCompact D)
    (kne : K.Nonempty) (kc : Convex ℝ K) (kk : IsCompact K)
    (b : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (leftCont : ∀ y ∈ K, Continuous (fun x => b x y))
    (rightCont : ∀ x ∈ D, Continuous (b x)) {c : ℝ}
    (h : ∀ y ∈ K, ∃ x ∈ D, b x y ≤ c) :
    ∃ x ∈ D, ∀ y ∈ K, b x y ≤ c := by
  obtain ⟨x, hx, y, hy, hs⟩ := Sion.exists_isSaddlePointOn
    (f := fun x y => b x y) dne dc dk
    (fun y hy => (leftCont y hy).lowerSemicontinuous.lowerSemicontinuousOn D)
    (fun y _ => ((b.flip y).convexOn dc).quasiconvexOn)
    kc kne kk
    (fun x hx => (rightCont x hx).upperSemicontinuous.upperSemicontinuousOn K)
    (fun x _ => ((b x).concaveOn kc).quasiconcaveOn)
  obtain ⟨z, hz, hzy⟩ := h y hy
  exact ⟨x, hx, fun w hw => (hs z hz w hw).trans hzy⟩

noncomputable def spectralMatrix (U : Matrix.unitaryGroup ι ℝ) (d : ι → ℝ) : M ι :=
  (Unitary.conjStarAlgAut ℝ (M ι) U) (Matrix.diagonal d)

theorem spectral_one (U : Matrix.unitaryGroup ι ℝ) :
    spectralMatrix U (fun _ => 1) = 1 := by simp [spectralMatrix]

theorem spectral_inv (U : Matrix.unitaryGroup ι ℝ) (d : ι → ℝ) (hn : ∀ i, d i ≠ 0) :
    (spectralMatrix U d)⁻¹ = spectralMatrix U (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  unfold spectralMatrix
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  simp [hn]

theorem trace_spectral (U : Matrix.unitaryGroup ι ℝ) (X : M ι) (d : ι → ℝ) :
    (X * spectralMatrix U d).trace =
      ∑ i, ((star (U : M ι)) * X * U) i i * d i := by
  rw [spectralMatrix, Unitary.conjStarAlgAut_apply, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

/-- The sharp upper bound for every individual feasible covariance, in arbitrary dimension. -/
theorem pointwise_upper {A P X : M ι} (hX : X.PosSemidef) (h1 : X.trace = 1)
    (hP : P.PosDef) (h : A * P + P * A.transpose = -X) (ht : 0 < -2 * A.trace) :
    (X * (1+P)⁻¹).trace ≤ (-2*A.trace) / (1 + (-2*A.trace)) := by
  let U := hP.isHermitian.eigenvectorUnitary
  let d := hP.isHermitian.eigenvalues
  let w : ι → ℝ := fun i => ((star (U : M ι)) * X * U) i i
  have hd : ∀ i, 0 < d i := hP.eigenvalues_pos
  have hdec : P = spectralMatrix U d := by
    simpa [spectralMatrix, U, d, Function.comp_def] using hP.isHermitian.spectral_theorem
  have hw : ∀ i, 0 ≤ w i := fun _ => (hX.conjTranspose_mul_mul_same (U : M ι)).diag_nonneg
  have hw1 : ∑ i, w i = 1 := by
    have htr := trace_spectral U X (fun _ => 1)
    simpa [w, spectral_one, h1] using htr.symm
  have mean : ∑ i, w i * (d i)⁻¹ = -2*A.trace := by
    rw [← trace_identity hP h, hdec, spectral_inv _ _ (fun i => (hd i).ne'), trace_spectral]
  have hplus : 1 + P = spectralMatrix U (fun i => 1 + d i) := by
    rw [hdec, ← spectral_one U]
    unfold spectralMatrix
    rw [← map_add, ← Matrix.diagonal_add]
  rw [hplus, spectral_inv _ _ (fun i => by have := hd i; positivity), trace_spectral]
  have hb := weighted_bound w (fun i => (d i)⁻¹) hw (fun i => inv_pos.mpr (hd i))
      hw1 ht mean (s := 1) zero_lt_one
  simp only [one_mul] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := hd i
  field_simp
  ring

/-- A semidefinite Gramian cap gives the required lower bound on the objective. -/
theorem lower_of_gramian_cap {P X : M ι} (hP : P.PosSemidef) (hX : X.PosSemidef)
    (h1 : X.trace = 1) {c : ℝ}
    (hcap : ∀ i, hP.isHermitian.eigenvalues i ≤ c) :
    (1+c)⁻¹ ≤ (X * (1+P)⁻¹).trace := by
  let U := hP.isHermitian.eigenvectorUnitary
  let d := hP.isHermitian.eigenvalues
  let w : ι → ℝ := fun i => ((star (U : M ι)) * X * U) i i
  have hd : ∀ i, 0 ≤ d i := hP.eigenvalues_nonneg
  have hdec : P = spectralMatrix U d := by
    simpa [spectralMatrix, U, d, Function.comp_def] using hP.isHermitian.spectral_theorem
  have hw : ∀ i, 0 ≤ w i := fun _ => (hX.conjTranspose_mul_mul_same (U : M ι)).diag_nonneg
  have hw1 : ∑ i, w i = 1 := by
    simpa [w, spectral_one, h1] using (trace_spectral U X (fun _ => 1)).symm
  have hplus : 1 + P = spectralMatrix U (fun i => 1 + d i) := by
    rw [hdec, ← spectral_one U]
    unfold spectralMatrix
    rw [← map_add, ← Matrix.diagonal_add]
  rw [hplus, spectral_inv _ _ (fun i => by have := hd i; positivity), trace_spectral]
  calc
    (1+c)⁻¹ = ∑ i, w i * (1+c)⁻¹ := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i * (1+d i)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by have := hd i; positivity) (by linarith [hcap i])

/-- Against each trace-one dual input, some Gramian eigenvalue is at most 1 / T. -/
theorem eigenvalue_at_most_inverse_trace {A Q Y : M ι}
    (hQ : Q.PosSemidef) (hY : Y.PosSemidef) (h1 : Y.trace = 1)
    (h : A * Q + Q * A.transpose = -Y) {T : ℝ} (hT : T = -2 * A.trace) (hpos : 0 < T) :
    ∃ i, hQ.isHermitian.eigenvalues i ≤ T⁻¹ := by
  by_contra! hall
  let U := hQ.isHermitian.eigenvectorUnitary
  let d := hQ.isHermitian.eigenvalues
  let w : ι → ℝ := fun i => ((star (U : M ι)) * Y * U) i i
  have hd : ∀ i, 0 < d i := fun i => (inv_pos.mpr hpos).trans (hall i)
  have hp : Q.PosDef := hQ.isHermitian.posDef_iff_eigenvalues_pos.mpr hd
  have hdec : Q = spectralMatrix U d := by
    simpa [spectralMatrix, U, d, Function.comp_def] using hQ.isHermitian.spectral_theorem
  have hw : ∀ i, 0 ≤ w i := fun _ => (hY.conjTranspose_mul_mul_same (U : M ι)).diag_nonneg
  have hw1 : ∑ i, w i = 1 := by
    simpa [w, spectral_one, h1] using (trace_spectral U Y (fun _ => 1)).symm
  have hmean : ∑ i, w i * (d i)⁻¹ = T := by
    rw [hT, ← trace_identity hp h, hdec, spectral_inv _ _ (fun i => (hd i).ne'), trace_spectral]
  have hsmall (i : ι) : (d i)⁻¹ < T := by
    have hi : T⁻¹ < d i := hall i
    rw [← one_div] at hi ⊢
    exact (div_lt_iff₀ (hd i)).mpr (by simpa [mul_comm] using (div_lt_iff₀ hpos).mp hi)
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra! hn
    have hz : ∀ i, w i = 0 := fun i => le_antisymm (hn i) (hw i)
    simp [hz] at hw1
  have contra : ∑ i, w i * (d i)⁻¹ < ∑ i, w i * T := by
    apply Finset.sum_lt_sum
    · exact fun i _ => mul_le_mul_of_nonneg_left (hsmall i).le (hw i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (hsmall j) hj⟩
  rw [hmean, ← Finset.sum_mul, hw1, one_mul] at contra
  exact (lt_irrefl T) contra

end LyapunovTrace
