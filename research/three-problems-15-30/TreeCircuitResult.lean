import TreeResult
import TreeSchedule
import Mathlib.Tactic

namespace Bacher.BirdSchedule
open scoped BigOperators

/-- A length-m dot product costs one AND and one XOR per edge, including
the initial XOR with zero. The two ports can be directly wired to whichever
rows of the incidence matrix the output gate needs. -/
def dotPlan (m : ℕ) : Expr m :=
  .total (fun e => .and (.orig e e) (.prev e e))

theorem gates_dotPlan (m : ℕ) : (dotPlan m).gates = 2*m := by
  simp [dotPlan, Expr.gates, two_mul]

/-- On a reduced incidence input B, construct the matrix for output j.
Its diagonal port reads ones when computing the replaced column. -/
def inputMatrix {n m : ℕ} (B : Matrix (Fin n) (Fin m) Bit) (j : Fin n) : Mat n :=
  Matrix.of (fun i k => (dotPlan m).eval
    (Matrix.of (fun e _ => B i e))
    (Matrix.of (fun e _ => if k = j then 1 else B k e)))

def output {n m : ℕ} (B : Matrix (Fin n) (Fin m) Bit) : Vector Bit n :=
  Vector.ofFn (fun j => compute (pack (inputMatrix B j)))

lemma inputMatrix_eq {n m : ℕ} (u v : Fin m → Option (Fin n)) (j : Fin n) :
    inputMatrix (incidence u v) j = incidence u v * testMatrix u v j := by
  ext i k
  by_cases h : k = j
  · subst k
    simp [inputMatrix, dotPlan, Expr.eval, Matrix.mul_apply, testMatrix, Matrix.updateCol_apply]
  · simp [inputMatrix, dotPlan, Expr.eval, Matrix.mul_apply, testMatrix, Matrix.updateCol_apply,
      h, Ne.symm h]

/-- All the bits of the product of rooted tree colorings are computed by one
uniformly generated circuit on the binary incidence matrix. -/
theorem output_correct {n m : ℕ} (u v : Fin m → Option (Fin n)) (j : Fin n) :
    (output (incidence u v))[j.val] = productBit u v j := by
  simp [output, compute_correct, inputMatrix_eq, partition_formula]

/-- For each output, n² dot-product preparations and one shared-layer
determinant evaluation. Constants and input-wire references are free. -/
def allGates (n m : ℕ) : ℕ := n * (n*n*(dotPlan m).gates + gateCount n)

theorem allGates_le (n m : ℕ) :
    allGates n m ≤ 2*m*n^3 + 3*n^5 + 2*n^4 := by
  unfold allGates
  rw [gates_dotPlan]
  have h := Nat.mul_le_mul_left n (Nat.add_le_add_left (gateCount_le n) (n*n*(2*m)))
  calc
    _ ≤ n * (n*n*(2*m) + n^3*(3*n+2)) := h
    _ = _ := by ring

#print axioms output_correct
#print axioms allGates_le
end Bacher.BirdSchedule
