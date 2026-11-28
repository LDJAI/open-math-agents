import OMAStatements.S_mo_492060

open OMA.S_mo_492060

namespace FanoCounterexample

-- The six lines of the source's Fano plane after deleting its first line
-- and changing labels from 1 through 7 to 0 through 6.
def sixLines : Family 7 :=
  {{0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}}

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem meets_conditions : admissible 4 3 sixLines := by
  unfold admissible
  decide

theorem misses_pair : ¬steiner 3 sixLines := by
  intro h
  let X : Finset (Fin 7) := {0,1}
  obtain ⟨B,hB,_⟩ := h X (by decide)
  have bad : ¬∃ B∈sixLines, X⊆B := by decide
  exact bad ⟨B,hB.1,hB.2⟩

end FanoCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_492060.main) := by
  intro claim
  exact FanoCounterexample.misses_pair
    (claim 4 3 (by decide) (by decide) (by decide) _ FanoCounterexample.meets_conditions)
