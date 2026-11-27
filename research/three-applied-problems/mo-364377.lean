import OMAStatements.S_mo_364377
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Orthogonal rounding fails in a neighborhood of a nearest signed permutation

Counterexample to MathOverflow 364377. The five by five Householder matrix
has diagonal entries 3/5 and off-diagonal entries -2/5. Its nearest signed
permutation includes the identity. The squared distance threshold is 1/4.
Source: https://mathoverflow.net/questions/364377
Credit: @LDJAI. Formalization assisted by Codex.
-/

/-!
A real orthogonal matrix with determinant minus one has trace at most its
dimension minus two. This proof uses rowwise Cauchy-Schwarz and the
nontrivial kernel of I+B, without spectral decomposition.
-/

open Matrix
open scoped Matrix BigOperators

namespace OrthogonalRounding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signed_trace_bound (B : Matrix ι ι ℝ)
    (ho : B * Bᵀ = 1) (hd : B.det = -1) :
    B.trace ≤ (Fintype.card ι : ℝ) - 2 := by
  classical
  have hh : (1 + B) * Bᵀ = (1 + B)ᵀ := by
    simp [add_mul, ho, add_comm]
  have hdet : (1 + B).det = 0 := by
    have hh' := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_transpose, hd, Matrix.det_transpose] at hh'
    linarith
  have hnu : ¬ IsUnit (1 + B) := by simp [Matrix.isUnit_iff_isUnit_det, hdet]
  obtain ⟨v, hv, hz⟩ : ∃ v : ι → ℝ, v ≠ 0 ∧ (1+B) *ᵥ v = 0 := by
    obtain ⟨a, b, hab⟩ := Function.not_injective_iff.mp
      (Matrix.mulVec_injective_iff_isUnit.not.mpr hnu)
    exact ⟨a-b, by simp [sub_eq_zero, hab, Matrix.mulVec_sub]⟩
  have hneg : B *ᵥ v = -v := by
    simpa [Matrix.add_mulVec, add_eq_zero_iff_eq_neg'] using hz
  let A : Matrix ι ι ℝ := 1 - B
  have hav : A *ᵥ v = v + v := by simp [A, Matrix.sub_mulVec, hneg, sub_neg_eq_add]
  let V := ∑ j, (v j)^2
  have hvpos : 0 < V := by
    have hne : v ⬝ᵥ v ≠ 0 := mt dotProduct_self_eq_zero.mp hv
    have hnon : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    simpa [V, dotProduct, sq] using lt_of_le_of_ne hnon (Ne.symm hne)
  have hrow (i : ι) : 4 * (v i)^2 ≤ (∑ j, (A i j)^2) * V := by
    have roweq := congrFun hav i
    change (∑ j, A i j * v j) = v i + v i at roweq
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) v
    rw [roweq] at h
    dsimp [V]
    nlinarith
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [← Finset.mul_sum, ← Finset.sum_mul] at htotal
  change 4 * V ≤ (∑ i, ∑ j, (A i j)^2) * V at htotal
  have hfrob := le_of_mul_le_mul_right htotal hvpos
  have htrace : (A * Aᵀ).trace = ∑ i, ∑ j, (A i j)^2 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
  have ha : A * Aᵀ = (1 - B) - (Bᵀ - 1) := by
    simp [A, sub_mul, mul_sub, ho]
  rw [← htrace, ha, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_transpose, Matrix.trace_one] at hfrob
  linarith

end OrthogonalRounding

open Matrix
open scoped Matrix BigOperators

noncomputable section

namespace OrthogonalRounding

abbrev M5 := Matrix (Fin 5) (Fin 5) ℝ
def c : ℝ := -2/5
def house : M5 := 1 + Matrix.of (fun _ _ => c)

theorem house_apply (i j : Fin 5) : house i j = (if i = j then 1 else 0) + c := by
  simp [house, Matrix.one_apply]

theorem house_orth : house * houseᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, house_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  by_cases h : i = j
  · subst j
    simp [c, ite_mul, mul_ite]
    norm_num
  · simp [h, c, ite_mul, mul_ite]
    norm_num

theorem house_det : house.det = -1 := by
  let u : Fin 5 → ℝ := fun _ => c
  let v : Fin 5 → ℝ := fun _ => 1
  have h : house = 1 + replicateCol Unit u * replicateRow Unit v := by
    ext i j
    simp [house, u, v, Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  norm_num [u, v, dotProduct, c]

theorem house_trace : house.trace = 3 := by
  norm_num [Matrix.trace, Matrix.diag, house_apply, c]

def signedPerm (σ : Equiv.Perm (Fin 5)) (s : Fin 5 → ℝ) : M5 :=
  Matrix.of (fun i j => if σ i = j then s i else 0)

def distanceSq (A B : M5) : ℝ := ∑ i, ∑ j, (A i j - B i j)^2

private theorem row_sq (x : Fin 5 → ℝ) (k : Fin 5) (s : ℝ) (hs : s^2=1) :
    (∑ j, (x j - (if k=j then s else 0))^2) =
    (∑ j, (x j)^2) + 1 - 2*s*x k := by
  have hh (j : Fin 5) : (x j - (if k=j then s else 0))^2 =
      (x j)^2 + (if k=j then (s^2-2*s*x k) else 0) := by
    by_cases e : k=j
    · subst j
      simp
      ring
    · simp [e]
  simp [hh, Finset.sum_add_distrib, hs]
  ring

theorem nearest_identity (σ : Equiv.Perm (Fin 5)) (s : Fin 5 → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    distanceSq house 1 ≤ distanceSq house (signedPerm σ s) := by
  apply Finset.sum_le_sum
  intro i hi
  change (∑ j, (house i j - (1 : M5) i j)^2) ≤
    ∑ j, (house i j - (if σ i=j then s i else 0))^2
  simp only [Matrix.one_apply]
  have hsq : s i ^ 2 = 1 := by rcases hs i with h|h <;> rw [h] <;> norm_num
  rw [row_sq _ _ _ (by norm_num), row_sq _ _ _ hsq]
  have hdiag : house i i = 3/5 := by norm_num [house_apply, c]
  have hentry : house i (σ i) = 3/5 ∨ house i (σ i) = -2/5 := by
    rw [house_apply]
    split_ifs <;> norm_num [c]
  rcases hentry with h|h <;> rcases hs i with hh|hh <;>
    rw [hdiag, h, hh] <;> linarith

private theorem diagonal_sq_le (A B : M5) (i : Fin 5) :
    (A i i - B i i)^2 ≤ distanceSq A B := by
  apply le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (A i j - B i j)) (Finset.mem_univ i))
  apply Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A k j - B k j)))
  exact Finset.mem_univ i

private theorem dist_trace (A B : M5) (ha : A * Aᵀ = 1) (hb : B * Bᵀ = 1) :
    distanceSq A B = 10 - 2 * (A * Bᵀ).trace := by
  have hsum (C : M5) : (∑ i, ∑ j, (C i j)^2) = (C*Cᵀ).trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
  have hex (i j : Fin 5) : (A i j - B i j)^2 =
      (A i j)^2 + (B i j)^2 - 2*(A i j*B i j) := by ring
  simp only [distanceSq, hex, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum A, hsum B, ha, hb]
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem no_improvement {B : M5} (hB : B * Bᵀ = 1) (hd : distanceSq house B < 1/4)
    (hweak : ∀ i, |house i i| ≤ |B i i|) :
    ¬ ∃ i, |house i i| < |B i i| := by
  rintro ⟨k, hk⟩
  have hdet := congrArg Matrix.det hB
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hsign : B.det = -1 := by
    by_contra h
    have hp : B.det = 1 := (mul_self_eq_one_iff.mp hdet).resolve_right h
    have hC : (house * Bᵀ) * (house * Bᵀ)ᵀ = 1 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      have hc : Bᵀ * B = 1 := mul_eq_one_comm.mp hB
      calc
        house * Bᵀ * (B * houseᵀ) = house * (Bᵀ * B) * houseᵀ := by
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hc, Matrix.mul_one, house_orth]
    have hs := signed_trace_bound _ hC (by simp [Matrix.det_mul, house_det, hp])
    have hc := dist_trace house B house_orth hB
    norm_num at hs
    linarith
  have htrace := signed_trace_bound B hB hsign
  have hp (i : Fin 5) : 0 < house i i := by norm_num [house_apply, c]
  have hbpos (i : Fin 5) : 0 < B i i := by
    have hh := diagonal_sq_le house B i
    norm_num [house_apply, c] at hh
    nlinarith [sq_nonneg (B i i)]
  have hle (i : Fin 5) : house i i ≤ B i i := by
    simpa [abs_of_pos (hp i), abs_of_pos (hbpos i)] using hweak i
  have hlt : house k k < B k k := by
    simpa [abs_of_pos (hp k), abs_of_pos (hbpos k)] using hk
  have ht : house.trace < B.trace :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨k, Finset.mem_univ _, hlt⟩
  rw [house_trace] at ht
  norm_num at htrace
  linarith

end OrthogonalRounding

open Matrix
open scoped Matrix BigOperators
open OrthogonalRounding OMA.S_mo_364377

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_364377.main) := by
  intro claim
  have horth : orthogonal house := mul_eq_one_comm.mp house_orth
  have hnot : ¬ signedPermutation house := by
    rintro ⟨σ, s, hs, he⟩
    have hh := he 0 0
    have h0 : house 0 0 = 3/5 := by norm_num [house_apply, c]
    rw [h0] at hh
    split_ifs at hh with e
    · rcases hs 0 with a|a <;> rw [a] at hh <;> norm_num at hh
    · norm_num at hh
  have hid : signedPermutation (1 : M5) := by
    refine ⟨Equiv.refl _, fun _ => 1, by simp, ?_⟩
    intro i j
    simp [Matrix.one_apply, eq_comm]
  have hnear : ∀ Q : M5, signedPermutation Q → frobSq house (1 : M5) ≤ frobSq house Q := by
    intro Q hQ
    obtain ⟨σ, s, hs, he⟩ := hQ
    have hQeq : Q = signedPerm σ s := by
      ext i j
      rw [he]
      simp [signedPerm, eq_comm]
    rw [hQeq]
    exact nearest_identity σ s hs
  obtain ⟨B, hb, hdb, hw, ⟨i, j, hs, ht⟩, _⟩ :=
    claim 5 house 1 horth hnot hid hnear (1/4) (by norm_num)
  have hdiag : i = j := by by_contra h; simp [Matrix.one_apply, h] at hs
  subst j
  exact no_improvement (mul_eq_one_comm.mp hb) hdb
    (fun k => hw k k (by simp)) ⟨i, ht⟩
