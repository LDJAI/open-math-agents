import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

namespace TreePartition
noncomputable section
open Finset Matrix

variable {n : ℕ} {E R : Type*} [Fintype E] [LinearOrder E] [CommRing R]

private def expansionTerm (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (f : Fin n → E) : R :=
  (∏ i, A i (f i)) * (B.submatrix f id).det

private theorem expandDet (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R) :
    (A * B).det = ∑ f, expansionTerm A B f := by
  classical
  let D := (Matrix.detRowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R).toMultilinearMap
  let g (i : Fin n) (e : E) : Fin n → R := A i e • B e
  have hM : (A * B) = fun i => ∑ e, g i e := by
    ext i j
    simp [Matrix.mul_apply, g, Finset.sum_apply]
  change D (A * B) = _
  rw [hM, D.map_sum g]
  apply Finset.sum_congr rfl
  intro f _
  exact Matrix.det_mul_column (fun i => A i (f i)) (B.submatrix f id)

private def mask (A : Matrix (Fin n) E R) (s : Finset E) : Matrix (Fin n) E R :=
  fun i e => if e ∈ s then A i e else 0

private theorem maskTerm (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (s : Finset E) (f : Fin n → E) :
    expansionTerm (mask A s) B f = if ∀ i, f i ∈ s then expansionTerm A B f else 0 := by
  classical
  by_cases h : ∀ i, f i ∈ s
  · simp [expansionTerm, mask, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    unfold expansionTerm
    have hz : (∏ j, mask A s j (f j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [mask, hi])
    simp [hz]

private theorem maskMul (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (s : Finset E) (hs : s.card = n) :
    mask A s * B = A.submatrix id (s.orderEmbOfFin hs) * B.submatrix (s.orderEmbOfFin hs) id := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, mask, ite_mul, zero_mul]
  let g (e : E) := A i e * B e j
  change (∑ e : E, if e ∈ s then g e else 0) = ∑ k : Fin n, g (s.orderEmbOfFin hs k)
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc ∑ e ∈ s, g e = ∑ e : s, g e := (s.sum_attach g).symm
       _ = _ := ((s.orderIsoOfFin hs).toEquiv.sum_comp fun e : s => g e).symm

/-- Cauchy–Binet, with minors indexed by increasing enumerations of edge subsets. -/
theorem cauchyBinet (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R) :
    (A*B).det = ∑ s : {s : Finset E // s.card = n},
      (A.submatrix id (s.1.orderEmbOfFin s.2)).det *
      (B.submatrix (s.1.orderEmbOfFin s.2) id).det := by
  classical
  let SS := {s : Finset E // s.card = n}
  calc
    (A * B).det = ∑ f, expansionTerm A B f := expandDet _ _
    _ = ∑ s : SS, ∑ f, expansionTerm (mask A s.1) B f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp_rw [maskTerm]
      by_cases hin : Function.Injective f
      · let s : {s : Finset E // s.card = n} :=
          ⟨Finset.univ.image f, by simp [Finset.card_image_of_injective _ hin]⟩
        symm
        rw [Finset.sum_eq_single s]
        · rw [if_pos (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
        · intro t _ hts
          apply if_neg
          intro h
          apply hts
          apply Subtype.ext
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro e he
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
            exact h i
          · exact t.2.trans s.2.symm |>.le
        · simp
      · have h : ∃ i j, f i = f j ∧ i ≠ j := by
          by_contra! ha
          exact hin fun i j hij => ha i j hij
        obtain ⟨i,j,hij,hne⟩ := h
        have hz : (B.submatrix f id).det = 0 :=
          Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij])
        simp [expansionTerm, hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← expandDet (mask A s.1) B, maskMul _ _ _ s.2, Matrix.det_mul]

end
end TreePartition
