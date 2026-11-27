module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two
import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.Tactic

/-! A uniform, layered Boolean circuit for the determinant over F₂.
Each layer reads materialized vectors from the preceding layer. Gate counts
come from the expressions that are actually evaluated. -/
@[expose] public section
namespace Bacher.BirdSchedule
open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Table (n : ℕ) := Vector (Vector Bit n) n
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) Bit

def pack {n : ℕ} (M : Mat n) : Table n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => M i j))

def read {n : ℕ} (T : Table n) : Mat n :=
  fun i j => (T[i.val])[j.val]

@[simp] theorem read_pack {n : ℕ} (M : Mat n) : read (pack M) = M := by
  ext i j
  simp [read, pack]

/-- Input and previous-layer references have no logic gates. A sum is a
left or right chain of n binary XORs seeded at zero. -/
inductive Expr (n : ℕ) where
  | zero
  | orig (i j : Fin n)
  | prev (i j : Fin n)
  | xor (a b : Expr n)
  | and (a b : Expr n)
  | total (terms : Fin n → Expr n)

def Expr.eval {n : ℕ} (A F : Mat n) : Expr n → Bit
  | .zero => 0
  | .orig i j => A i j
  | .prev i j => F i j
  | .xor a b => a.eval A F + b.eval A F
  | .and a b => a.eval A F * b.eval A F
  | .total f => ∑ k, (f k).eval A F

def Expr.gates {n : ℕ} : Expr n → ℕ
  | .zero | .orig _ _ | .prev _ _ => 0
  | .xor a b | .and a b => a.gates + b.gates + 1
  | .total f => n + ∑ k, (f k).gates

def cell {n : ℕ} (i j : Fin n) : Expr n :=
  .xor (.and (.total (fun k => if i < k then .prev k k else .zero)) (.orig i j))
    (.total (fun k => if i < k then .and (.prev i k) (.orig k j) else .zero))

private theorem sum_tail {n : ℕ} (i : Fin n) (f : Fin n → Bit) :
    (∑ k, if i < k then f k else 0) = ∑ k ∈ Finset.Ioi i, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

theorem eval_cell {n : ℕ} (A F : Mat n) (i j : Fin n) :
    (cell i j).eval A F = BirdDet.Spec.stepEntry A F i j := by
  simp only [cell, Expr.eval, BirdDet.Spec.stepEntry_eq, Matrix.of_apply,
    apply_ite (Expr.eval A F), ZMod.neg_eq_self_mod_two, sum_tail]

theorem gates_cell {n : ℕ} (i j : Fin n) : (cell i j).gates ≤ 3*n + 2 := by
  have h₁ : (∑ k : Fin n, (if i < k then (Expr.prev k k) else .zero).gates) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    split <;> rfl
  have h₂ : (∑ k : Fin n, (if i < k then (Expr.and (.prev i k) (.orig k j)) else .zero).gates) ≤ n := by
    calc
      _ ≤ ∑ _k : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro k _
        split <;> simp [Expr.gates]
      _ = _ := by simp
  simp only [cell, Expr.gates] at *
  omega

/-- Labeled copies of intermediate scalar values are retained exactly once
per layer, independently of the fan-out to the following layer. -/
def layers {n : ℕ} (A : Table n) : ℕ → Table n
  | 0 => A
  | t+1 =>
    let F := layers A t
    pack (Matrix.of (fun i j => (cell i j).eval (read A) (read F)))

theorem read_layers {n : ℕ} (A : Table n) (t : ℕ) :
    read (layers A t) = (BirdDet.Spec.stepEntry (read A))^[t] (read A) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [layers, read_pack, Function.iterate_succ_apply']
    ext i j
    exact (eval_cell _ _ _ _).trans (by rw [ih])

def compute : {n : ℕ} → Table n → Bit
  | 0, _ => 1
  | k+1, A => (read (layers A k)) 0 0

theorem compute_correct {n : ℕ} (A : Table n) : compute A = Matrix.det (read A) := by
  rw [BirdDet.birdDetSpec_eq_det]
  cases n with
  | zero => simp [compute]
  | succ k =>
    rw [BirdDet.Spec.birdDetSpec_succ, ZMod.neg_eq_self_mod_two, one_pow, one_mul]
    simp only [compute, read_layers]

/-- Gate count of the same materialized traversal, excluding input wiring. -/
def gateCount (n : ℕ) : ℕ := (n-1) * ∑ i : Fin n, ∑ j : Fin n, (cell i j).gates

theorem gateCount_le (n : ℕ) : gateCount n ≤ n^3 * (3*n+2) := by
  have hh : (∑ i : Fin n, ∑ j : Fin n, (cell i j).gates) ≤ n*(n*(3*n+2)) := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (3*n+2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => gates_cell i j))
      _ = _ := by simp
  calc
    gateCount n ≤ n * (n*(n*(3*n+2))) := Nat.mul_le_mul (Nat.sub_le ..) hh
    _ = _ := by ring

end Bacher.BirdSchedule
