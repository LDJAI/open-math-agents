import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Bacher.Elimination
open Matrix

abbrev Bit := ZMod 2
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) Bit

/-- Evaluate all entries once and store the result in vectors before the next pivot step. -/
def tabulate {n : ℕ} (f : Square n) : Square n :=
  let rows := Vector.ofFn (fun i : Fin n => Vector.ofFn (f i))
  fun i j => rows[i.val][j.val]

@[simp] theorem tabulate_eq {n : ℕ} (f : Square n) : tabulate f = f := by
  ext i j
  simp [tabulate]

def firstPivot {n : ℕ} (A : Square n) (j : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (A i j = 1))

def residual {n : ℕ} (A : Square (n+1)) (p : Fin (n+1)) : Square n :=
  fun i j => A (p.succAbove i) j.succ + A (p.succAbove i) 0 * A p j.succ

/-- The second component charges one bit comparison per possible pivot, one AND and
one XOR per entry of the smaller table. It bounds arithmetic work including a full scan. -/
def solve : (n : ℕ) → Square n → Bit × ℕ
  | 0, _ => (1, 0)
  | n+1, A =>
    match firstPivot A 0 with
    | none => (0, n+1)
    | some p =>
      let r := solve n (tabulate (residual A p))
      (r.1, r.2 + (n+1) + 2*n*n)

theorem det_residual {n : ℕ} (A : Square (n+1)) (p : Fin (n+1))
    (hp : A p 0 = 1) : A.det = (residual A p).det := by
  let c (i : Fin (n+1)) : Bit := if i = p then 0 else A i 0
  let T : Square (n+1) := fun i j => A i j + c i * A p j
  have hd : T.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c p (by simp [c]) (fun _ _ => rfl)
  have h0 : T p 0 = 1 := by simp [T, c, hp]
  have hz (i) (hi : i ≠ p) : T i 0 = 0 := by
    simp [T, c, hi, hp, CharTwo.add_self_eq_zero]
  have hR : T.submatrix p.succAbove Fin.succ = residual A p := by
    ext i j
    change A (p.succAbove i) j.succ + c (p.succAbove i) * A p j.succ = _
    simp [c, residual, Fin.succAbove_ne]
  rw [← hd, Matrix.det_succ_column_zero, Finset.sum_eq_single p]
  · rw [h0, hR, ZMod.neg_eq_self_mod_two]
    simp
  · intro i _ hi
    simp [hz i hi]
  · simp

theorem all_zero {n : ℕ} (A : Square (n+1)) (h : firstPivot A 0 = none) :
    A.det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  have hn : A i 0 ≠ 1 := by
    have ha := List.find?_eq_none.mp h i (by simp)
    simpa using ha
  generalize he : A i 0 = b at hn ⊢
  fin_cases b <;> first | rfl | exact (hn rfl).elim

/-- Correctness and worst-case bit-arithmetic bound for a deterministic tabulated solver. -/
theorem solve_spec (n : ℕ) (A : Square n) :
    (solve n A).1 = A.det ∧ (solve n A).2 ≤ 3*n^3 := by
  induction n with
  | zero => simp [solve]
  | succ n ih =>
    cases he : firstPivot A 0 with
    | none =>
      simp only [solve, he]
      refine ⟨(all_zero A he).symm, ?_⟩
      nlinarith only [Nat.zero_le n, Nat.zero_le (n*n), Nat.zero_le (n*n*n)]
    | some p =>
      have hp : A p 0 = 1 := by
        simpa using (List.find?_some he)
      obtain ⟨hval, hcost⟩ := ih (tabulate (residual A p))
      simp only [solve, he]
      refine ⟨hval.trans ?_, ?_⟩
      · rw [tabulate_eq, ← det_residual A p hp]
      · nlinarith only [hcost, Nat.zero_le n, Nat.zero_le (n*n)]

end Bacher.Elimination
