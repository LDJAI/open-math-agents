import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace TreeParity
open Matrix
open scoped Matrix
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]

lemma bit_sq (z : ZMod 2) : z * z = z := by
  fin_cases z <;> rfl

lemma gram_diag (B : Matrix n m (ZMod 2)) : (B * Bᵀ).diag = B *ᵥ (fun _ => 1) := by
  funext i
  simp only [diag_apply, mul_apply, transpose_apply, bit_sq, mulVec, dotProduct, mul_one]

/-- The vector of Cramer determinants used by the spanning-tree algorithm collapses
to zero when the number of spanning trees is even. -/
theorem cramer_gram (B : Matrix n m (ZMod 2)) :
    cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = (B * Bᵀ).det • (B * Bᵀ).adjugate.diag := by
  let L := B * Bᵀ
  let A := L.adjugate
  have hL : Lᵀ = L := by simp [L,transpose_mul]
  have hA : Aᵀ = A := by simp [A,adjugate_transpose,hL]
  change cramer L (B *ᵥ fun _ => 1) = L.det • A.diag
  rw [cramer_eq_adjugate_mulVec, mulVec_mulVec]
  change (A * B) *ᵥ (fun _ => 1) = L.det • A.diag
  rw [← gram_diag, transpose_mul, hA, Matrix.mul_assoc, ← Matrix.mul_assoc B,
    ← Matrix.mul_assoc A]
  change ((L.adjugate * L) * A).diag = _
  rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul, diag_smul]

theorem cramer_singular (B : Matrix n m (ZMod 2)) (h : (B * Bᵀ).det = 0) :
    cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = 0 := by rw [cramer_gram,h,zero_smul]

theorem solve_nonsingular (B : Matrix n m (ZMod 2)) (h : (B * Bᵀ).det ≠ 0) :
    (B * Bᵀ) *ᵥ cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = B *ᵥ fun _ => 1 := by
  have hOne : (B * Bᵀ).det = 1 := by
    generalize hz : (B * Bᵀ).det = z at h ⊢
    fin_cases z <;> first | rfl | exact (h rfl).elim
  rw [Matrix.mulVec_cramer, hOne, one_smul]

end TreeParity
