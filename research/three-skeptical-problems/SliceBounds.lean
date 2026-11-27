import OMAStatements.S_mo_184507
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Necessary conditions on the length profile of a graph on the closed square. -/

namespace SliceBounds

open OMA.S_mo_184507

private noncomputable def speed (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (1 + (fderivWithin ℝ f square z (1, 0)) ^ 2)

private lemma speed_continuousOn {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f square) :
    ContinuousOn (speed f) square := by
  have hu : UniqueDiffOn ℝ square := uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hD := hf.continuousOn_fderivWithin hu le_rfl
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.add ((hD.clm_apply continuousOn_const).pow 2))

private noncomputable def clip (x : ℝ) := max 0 (min 1 x)

private lemma clip_mem (x : ℝ) : clip x ∈ interval :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma clip_eq {x : ℝ} (hx : x ∈ interval) : clip x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

/-- The length profile of every continuously differentiable graph is continuous,
including at both ends of the parameter interval. -/
theorem continuousOn_sliceLength {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f square) :
    ContinuousOn (sliceLength f) interval := by
  let g : ℝ → ℝ → ℝ := fun y x => speed f (clip x, clip y)
  have hc : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hg : Continuous (Function.uncurry g) :=
    (speed_continuousOn hf).comp_continuous ((hc.comp continuous_snd).prodMk
      (hc.comp continuous_fst)) (fun z => ⟨clip_mem _, clip_mem _⟩)
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hg 0 1).continuousOn.congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ interval := by simpa [interval, Set.uIcc_of_le zero_le_one] using hx
  simp [g, speed, clip_eq hx', clip_eq hy]

/-- Every horizontal graph slice has length at least the width of the square. -/
theorem one_le_sliceLength {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f square)
    {y : ℝ} (hy : y ∈ interval) : 1 ≤ sliceLength f y := by
  have hc : ContinuousOn (fun x => speed f (x,y)) interval :=
    (speed_continuousOn hf).comp (continuousOn_id.prodMk continuousOn_const)
      (fun x hx => ⟨hx, hy⟩)
  have hi : IntervalIntegrable (fun x => speed f (x,y)) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hc
  have low (x : ℝ) (_ : x ∈ Set.Icc (0 : ℝ) 1) : 1 ≤ speed f (x,y) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg _))
  have h := intervalIntegral.integral_mono_on zero_le_one (f := fun _ : ℝ => (1 : ℝ))
    (intervalIntegrable_const) hi low
  simpa [sliceLength, speed] using h

/-- Realizing all admissible length profiles refutes differentiability by choosing
one with a corner at the midpoint of the rectangle. -/
theorem disproof_of_prescription
    (realize : ∀ L : ℝ → ℝ, ContinuousOn L interval → (∀ y ∈ interval, 1 ≤ L y) →
      ∃ f : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 f square ∧ Set.EqOn (sliceLength f) L interval) :
    ¬ (type_of% @OMA.S_mo_184507.main) := by
  intro universal
  let L : ℝ → ℝ := fun y => 1 + |y - 1/2|
  have hL : Continuous L := continuous_const.add (continuous_id.sub continuous_const).abs
  obtain ⟨f, hf, hprofile⟩ := realize L hL.continuousOn (fun y _ => le_add_of_nonneg_right (abs_nonneg _))
  have smooth : ContDiffOn ℝ 1 L interval := (universal f hf).congr hprofile.symm
  have near : interval ∈ nhds (1/2 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hd : DifferentiableAt ℝ L (1/2) :=
    (smooth.contDiffAt near).differentiableAt (by norm_num)
  have shift : DifferentiableAt ℝ (fun t : ℝ => t + 1/2) 0 := differentiableAt_id.add_const _
  have hd' : DifferentiableAt ℝ L ((fun t : ℝ => t + 1/2) 0) := by simpa using hd
  have hcomp := (hd'.comp 0 shift).sub_const 1
  apply not_differentiableAt_abs_zero
  have hsame : (fun y : ℝ => (L ∘ fun t => t + 1/2) y - 1) = abs := by
    funext t
    simp [L]
  rwa [hsame] at hcomp

end SliceBounds

#print axioms SliceBounds.continuousOn_sliceLength
#print axioms SliceBounds.one_le_sliceLength
#print axioms SliceBounds.disproof_of_prescription
