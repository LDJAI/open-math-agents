import TreeColor
import TreeBinet

namespace Bacher
open Matrix
open scoped Matrix
variable {n m : ℕ}

/-- One determinant of order n per requested color bit, on n+1 vertices. -/
theorem partition_formula (u v : Fin m → Option (Fin n)) (j : Fin n) :
    ((incidence u v) * (testMatrix u v j)).det = productBit u v j := by
  classical
  rw [TreePartition.cauchyBinet, productBit]
  apply Finset.sum_congr rfl
  intro s _
  exact summand u v s j

/-- Writing the same algorithm directly on the grounded Laplacian. -/
theorem laplacian_formula (u v : Fin m → Option (Fin n)) (j : Fin n) :
    (((incidence u v) * (incidence u v).transpose).updateCol j
      ((incidence u v) *ᵥ fun _ => 1)).det = productBit u v j := by
  rw [← partition_formula]
  congr 1
  ext i k
  by_cases hk : k = j
  · subst k
    simp [testMatrix, Matrix.mul_apply, Matrix.updateCol_apply, Matrix.mulVec, dotProduct]
  · simp [testMatrix, Matrix.mul_apply, Matrix.updateCol_apply, hk, Ne.symm hk]

end Bacher
