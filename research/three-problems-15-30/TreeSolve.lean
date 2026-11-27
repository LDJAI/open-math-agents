import TreeElimination
import TreeFast
import Mathlib.Tactic.Ring

namespace Bacher.Elimination
open Matrix
open scoped Matrix

abbrev Column (n : ℕ) := Fin n → Bit

def cacheVec {n} (v : Column n) : Column n :=
  let a := Vector.ofFn v
  fun i => a[i.val]

@[simp] theorem cacheVec_eq {n} (v : Column n) : cacheVec v = v := by
  funext i
  simp [cacheVec]

def reduceVec {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1)) : Column n :=
  fun i => b (p.succAbove i) + A (p.succAbove i) 0 * b p

def tailSum {n} (A : Square (n+1)) (i : Fin (n+1)) (y : Column n) : Bit :=
  ∑ j, A i j.succ * y j

def recover {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1)) (y : Column n) :
    Column (n+1) :=
  Fin.cons (b p + tailSum A p y) y

/-- The charge counts pivot comparisons, field additions and multiplications with
one slot per operation. A stage may charge unused slots if it terminates early. -/
def linearSolve : (n : ℕ) → Square n → Column n → Option (Column n) × ℕ
  | 0, _, _ => (some (fun _ => 0), 0)
  | n+1, A, b =>
    match firstPivot A 0 with
    | none => (none, n+1)
    | some p =>
      let r := linearSolve n (tabulate (residual A p)) (cacheVec (reduceVec A b p))
      (r.1.map (fun y => cacheVec (recover A b p y)), r.2 + 2*n*n + 5*n + 2)

private theorem recover_correct {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1))
    (y : Column n) (hp : A p 0 = 1) (hy : residual A p *ᵥ y = reduceVec A b p) :
    A *ᵥ recover A b p y = b := by
  funext i
  change (∑ j, A i j * recover A b p y j) = b i
  rw [Fin.sum_univ_succ]
  change A i 0 * (b p + tailSum A p y) + tailSum A i y = b i
  by_cases h : i = p
  · subst i
    rw [hp, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
    have he := congrFun hy j
    change (∑ k, (A (p.succAbove j) k.succ + A (p.succAbove j) 0 * A p k.succ) * y k) =
      b (p.succAbove j) + A (p.succAbove j) 0 * b p at he
    rw [hj] at he
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at he
    change tailSum A i y + A i 0 * tailSum A p y = b i + A i 0 * b p at he
    calc A i 0 * (b p + tailSum A p y) + tailSum A i y
          = A i 0 * b p + (tailSum A i y + A i 0 * tailSum A p y) := by ring
         _ = A i 0 * b p + (b i + A i 0 * b p) := by rw [he]
         _ = b i := by rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem linearSolve_spec (n : ℕ) (A : Square n) (b : Column n) :
    (match (linearSolve n A b).1 with
     | none => A.det = 0
     | some x => A.det ≠ 0 ∧ A *ᵥ x = b) ∧
    (linearSolve n A b).2 ≤ 7*n^3 := by
  induction n with
  | zero =>
    simp only [linearSolve, Matrix.det_fin_zero, ne_eq, one_ne_zero, not_false_eq_true, true_and]
    exact ⟨Subsingleton.elim _ _, by decide⟩
  | succ n ih =>
    cases he : firstPivot A 0 with
    | none =>
      simp only [linearSolve, he]
      refine ⟨all_zero A he, ?_⟩
      nlinarith only [Nat.zero_le n, Nat.zero_le (n*n), Nat.zero_le (n*n*n)]
    | some p =>
      have hp : A p 0 = 1 := by simpa using (List.find?_some he)
      have hd := det_residual A p hp
      have ⟨hval,hcost⟩ := ih (tabulate (residual A p)) (cacheVec (reduceVec A b p))
      simp only [linearSolve, he]
      constructor
      · cases hr : (linearSolve n (tabulate (residual A p)) (cacheVec (reduceVec A b p))).1 with
        | none =>
          rw [hr] at hval
          simpa only [Option.map_none, hd, tabulate_eq] using hval
        | some y =>
          rw [hr] at hval
          simp only [tabulate_eq, cacheVec_eq] at hval
          simpa only [Option.map_some, cacheVec_eq] using
            And.intro (hd.trans_ne hval.1) (recover_correct A b p y hp hval.2)
      · nlinarith only [hcost, Nat.zero_le n, Nat.zero_le (n*n)]

/-- One execution returns every color simultaneously, returning zero on breakdown. -/
def colors {n m} (u v : Fin m → Option (Fin n)) : Column n :=
  let A := incidence u v
  let L := tabulate (A * A.transpose)
  let b := cacheVec (A *ᵥ (fun _ => 1))
  (linearSolve n L b).1.getD (fun _ => 0)

theorem colors_correct {n m} (u v : Fin m → Option (Fin n)) : colors u v = productBit u v := by
  let L := groundedLap u v
  let b := incidence u v *ᵥ fun _ => 1
  have h := (linearSolve_spec n L b).1
  simp only [colors, tabulate_eq, cacheVec_eq]
  change (linearSolve n L b).1.getD _ = _
  cases hr : (linearSolve n L b).1 with
  | none =>
    rw [hr] at h
    exact (singular_trivial _ _ h).symm
  | some x =>
    rw [hr] at h
    exact (nonsingular_eq_solve u v h.1 x).mpr h.2

end Bacher.Elimination
