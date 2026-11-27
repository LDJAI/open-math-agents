import GridCore

namespace GridCounter

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact numbers of connected spanning subgraphs in the two orientations. -/
theorem nineteen_eighteen : count 4 2 4 19 18 = 3780 := by decide +kernel
theorem eighteen_nineteen : count 4 2 4 18 19 = 3779 := by decide +kernel

def assertion : Prop :=
  ∀ n x y m p : Nat, x ≤ n → y ≤ n → x < y → p < m → count n x y m p ≤ count n x y p m

theorem disproof : ¬ assertion := by
  intro h
  have wrong := h 4 2 4 19 18 (by decide) (by decide) (by decide) (by decide)
  rw [nineteen_eighteen,eighteen_nineteen] at wrong
  exact (by decide : ¬(3780 ≤ 3779)) wrong

#print axioms disproof
end GridCounter
