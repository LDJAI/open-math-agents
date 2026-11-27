import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

open Matrix

/-- A positive 2 by 2 matrix over a possibly noncommutative ordered star ring
is bounded by twice the constant diagonal formed from its (unnormalized)
trace. Matrix order is stated as positive semidefiniteness of the difference. -/
theorem partialTraceBlockBound {R : Type*} [Ring R] [PartialOrder R]
    [StarRing R] [AddLeftMono R] (A : Matrix (Fin 2) (Fin 2) R)
    (hA : A.PosSemidef) :
    (2 • Matrix.diagonal (fun _ : Fin 2 => A 0 0 + A 1 1) - A).PosSemidef := by
  let Z : Matrix (Fin 2) (Fin 2) R := !![1,0;0,-1]
  let X : Matrix (Fin 2) (Fin 2) R := !![0,1;1,0]
  let Y : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,0]
  have hid : 2 • Matrix.diagonal (fun _ : Fin 2 => A 0 0 + A 1 1) - A =
      Zᴴ * A * Z + Xᴴ * A * X + Yᴴ * A * Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Z, X, Y, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.diagonal, two_mul] <;> abel
  rw [hid]
  exact ((hA.conjTranspose_mul_mul_same Z).add
    (hA.conjTranspose_mul_mul_same X)).add (hA.conjTranspose_mul_mul_same Y)

#print axioms partialTraceBlockBound
