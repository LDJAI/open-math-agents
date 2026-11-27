import TreeIncidence
import TreeElimination
import Mathlib.Algebra.BigOperators.Fin

namespace Bacher.Input
open Matrix
open scoped Matrix
abbrev Bit := ZMod 2

/-- Dot product by an explicit bounded loop, returning its bit-operation charge. -/
def inner : (m : ℕ) → (Fin m → Bit) → (Fin m → Bit) → Bit × ℕ
  | 0, _, _ => (0, 0)
  | m+1, a, b =>
    let z := inner m (fun i => a i.castSucc) (fun i => b i.castSucc)
    (z.1 + a (Fin.last m) * b (Fin.last m), z.2+2)

theorem inner_spec {m : ℕ} (a b : Fin m → Bit) :
    inner m a b = (∑ i, a i * b i, 2*m) := by
  induction m with
  | zero => simp [inner]
  | succ m ih => simp [inner, ih, Fin.sum_univ_castSucc, Nat.mul_succ]

/-- Materialize each incidence entry once, including endpoint and root comparisons. -/
def columns {n m : ℕ} (u v : Fin m → Option (Fin n)) : Matrix (Fin n) (Fin m) Bit :=
  let rows := Vector.ofFn fun i : Fin n => Vector.ofFn (incidence u v i)
  fun i e => rows[i.val][e.val]

theorem columns_eq {n m : ℕ} (u v : Fin m → Option (Fin n)) : columns u v = incidence u v := by
  ext; simp [columns]

structure Data (n : ℕ) where
  matrix : Elimination.Square n
  rhs : Fin n → Bit
  cost : ℕ

/-- Assemble the matrix and right-hand side using only endpoint tests and bit arithmetic.
The cost charges three operations per incidence entry, two per dot-product term. -/
def prepare {n m : ℕ} (u v : Fin m → Option (Fin n)) : Data n :=
  let B := columns u v
  let entries := Vector.ofFn fun i : Fin n =>
    Vector.ofFn fun j : Fin n => inner m (B i) (B j)
  let right := Vector.ofFn fun i : Fin n => inner m (B i) (fun _ => 1)
  ⟨fun i j => (entries[i.val][j.val]).1, fun i => (right[i.val]).1,
    3*n*m + (∑ i : Fin n, ∑ j : Fin n, (entries[i.val][j.val]).2) +
      ∑ i : Fin n, (right[i.val]).2⟩

theorem prepare_spec {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (prepare u v).matrix = (incidence u v)*(incidence u v).transpose ∧
    (prepare u v).rhs = (incidence u v) *ᵥ (fun _ => 1) ∧
    (prepare u v).cost = 3*n*m + n*(n*(2*m)) + n*(2*m) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [prepare, columns_eq, inner_spec, Matrix.mul_apply]
  · funext i; simp [prepare, columns_eq, inner_spec, Matrix.mulVec, dotProduct]
  · simp [prepare, inner_spec, Finset.sum_const, Nat.smul_one_eq_cast]

end Bacher.Input
