import TreeInput
import TreeSolve

namespace Bacher
open Matrix
open scoped Matrix

/-- Uniform endpoint-list algorithm. The first component is the color of every
nonroot vertex. The second accounts for the loop work specified by Input.prepare
and Elimination.linearSolve. The distinguished root has color zero. -/
def partitionAlgorithm {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (Fin n → ZMod 2) × ℕ :=
  let data := Input.prepare u v
  let solve := Elimination.linearSolve n data.matrix data.rhs
  (solve.1.getD (fun _ => 0), data.cost + solve.2)

theorem partitionAlgorithm_spec {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (partitionAlgorithm u v).1 = productBit u v ∧
    (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨hmat,hrhs,hc⟩ := Input.prepare_spec u v
  dsimp only [partitionAlgorithm]
  rw [hmat, hrhs, hc]
  constructor
  · simpa only [Elimination.colors, Elimination.tabulate_eq, Elimination.cacheVec_eq] using
      Elimination.colors_correct u v
  · exact Nat.add_le_add_left (Elimination.linearSolve_spec n _ _).2 _

end Bacher
