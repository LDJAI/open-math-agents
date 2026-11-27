import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! A certificate about the particular Paley tournament on 67 vertices.
This does not assume that 67 is the minimum order for domination number 5. -/
namespace PaleyCertificate

abbrev V := Fin 67

/-- The nonzero quadratic residues modulo 67 specify the winning direction. -/
def beats (x y : V) : Prop :=
  x ≠ y ∧ (List.range 67).any
    (fun i => (i * i) % 67 == (y.val + 67 - x.val) % 67) = true

instance (x y : V) : Decidable (beats x y) := by unfold beats; infer_instance

def prescribed : Finset V := {0,1,2,5}
def witnesses : Finset V := {13,32,43,46,53}
def cover : Finset V := {0,1,2,3,20}

def Dominates (S : Finset V) : Prop := ∀ v, v ∈ S ∨ ∃ u ∈ S, beats u v

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem five_dominate : Dominates cover := by
  unfold Dominates
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private theorem common_witness :
    ∀ w ∈ witnesses, w ∉ prescribed ∧ ∀ u ∈ prescribed, ¬ beats u w := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private theorem avoid_every_vertex :
    ∀ v : V, ∃ w ∈ witnesses, w ≠ v ∧ ¬ beats v w := by decide

/-- No possible fifth candidate extends this prescribed four to a cover. -/
theorem four_do_not_extend (v : V) : ¬ Dominates (insert v prescribed) := by
  intro h
  obtain ⟨w,hw,hne,hn⟩ := avoid_every_vertex v
  rcases h w with hm | ⟨u,hu,hub⟩
  · rcases Finset.mem_insert.mp hm with he | hp
    · exact hne he
    · exact (common_witness w hw).1 hp
  · rcases Finset.mem_insert.mp hu with rfl | hp
    · exact hn hub
    · exact (common_witness w hw).2 _ hp hub

end PaleyCertificate
