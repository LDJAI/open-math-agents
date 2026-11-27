import TreeAlgorithm
import Mathlib.Tactic.FinCases

namespace Bacher.Example
/-- Edges of the triangle on the root, 0 and 1, and a leaf 2 at the root. -/
def leftEnd (e : Fin 4) : Option (Fin 3) :=
  if e = 1 then some 0 else if e = 2 then some 1 else none
def rightEnd (e : Fin 4) : Option (Fin 3) :=
  if e = 0 then some 0 else if e = 1 then some 1 else if e = 3 then some 2 else none

theorem triangle_with_leaf : productBit leftEnd rightEnd = fun i => if i = 2 then 1 else 0 := by
  rw [← (partitionAlgorithm_spec leftEnd rightEnd).1]
  funext i
  fin_cases i <;> decide +kernel

end Bacher.Example
