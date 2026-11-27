import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

open scoped CStarAlgebra

/-- An injective complex star-algebra endomorphism reflects the C*-order. -/
theorem faithfulStarAlgHom_le_iff {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [IsOrderedAddMonoid A] (r : A →⋆ₐ[ℂ] A)
    (hr : Function.Injective r) (u v : A) : r u ≤ r v ↔ u ≤ v := by
  suffices h : ∀ x : A, 0 ≤ r x ↔ 0 ≤ x by
    rw [← sub_nonneg, ← map_sub, h, sub_nonneg]
  intro x
  constructor
  · intro hx
    have hs : IsSelfAdjoint x := by
      apply hr
      rw [map_star, hx.isSelfAdjoint.star_eq]
    have hn := (CFC.negPart_eq_zero_iff (r x) hx.isSelfAdjoint).mpr hx
    apply (CFC.negPart_eq_zero_iff x hs).mp
    apply hr
    rw [map_zero, CFC.negPart_def]
    rw [NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) r (fun y : ℝ => y⁻) x
      (ha := hs) (hφa := hx.isSelfAdjoint)]
    exact hn
  · intro hx
    have hs : IsSelfAdjoint (r x) := by
      change star (r x) = r x
      rw [← map_star, hx.isSelfAdjoint.star_eq]
    apply (CFC.negPart_eq_zero_iff (r x) hs).mp
    have hn := (CFC.negPart_eq_zero_iff x hx.isSelfAdjoint).mpr hx
    rw [CFC.negPart_def] at hn ⊢
    rw [← NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) r (fun y : ℝ => y⁻) x
      (ha := hx.isSelfAdjoint) (hφa := hs), hn, map_zero]
#print axioms faithfulStarAlgHom_le_iff
