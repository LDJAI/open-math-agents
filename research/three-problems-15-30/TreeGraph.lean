import TreeColor
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Bacher
variable {n m : ℕ}

/-- The ordinary simple graph obtained from indexed endpoints, ignoring orientation. -/
def endpointGraph (u v : Fin m → Option (Fin n)) := SimpleGraph.fromRel (Adjacent u v)

theorem reachable_iff_generated (u v : Fin m → Option (Fin n)) (p q : Option (Fin n)) :
    (endpointGraph u v).Reachable p q ↔ Relation.EqvGen (Adjacent u v) p q := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact .refl _
    | cons edge _ ih =>
      rcases edge.2 with h | h
      · exact .trans _ _ _ (.rel _ _ h) ih
      · exact .trans _ _ _ (.symm _ _ (.rel _ _ h)) ih
  · intro h
    induction h with
    | rel p q h =>
      by_cases he : p=q
      · subst q; exact .refl _
      · exact SimpleGraph.Adj.reachable (G := endpointGraph u v) ⟨he, Or.inl h⟩
    | refl p => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hp hq => exact hp.trans hq

theorem graph_connected (u v : Fin m → Option (Fin n)) :
    (endpointGraph u v).Connected ↔ Connected u v := by
  refine ⟨fun h p => (reachable_iff_generated u v none p).mp (h none p), ?_⟩
  intro h
  have hr (p) := (reachable_iff_generated u v none p).mpr (h p)
  exact ⟨fun p q => (hr p).symm.trans (hr q)⟩

theorem graph_isTree_of_card (u v : Fin n → Option (Fin n))
    (hcard : Nat.card (endpointGraph u v).edgeSet = n) :
    (endpointGraph u v).IsTree ↔ Connected u v := by
  rw [SimpleGraph.isTree_iff_connected_and_card, graph_connected, hcard]
  simp [Nat.card_eq_fintype_card]

lemma Walk_length_parity {α : Type} {G : SimpleGraph α} (c : α → ZMod 2)
    (hc : ∀ {a b}, G.Adj a b → c a + c b = 1) {p q : α} (w : G.Walk p q) :
    c p + c q = (w.length : ZMod 2) := by
  induction w with
  | nil => simp [CharTwo.add_self_eq_zero]
  | @cons a b z edge tail ih =>
    calc
      c a + c z = (c a + c b) + (c b + c z) := by
        rw [add_assoc (c a), ← add_assoc (c b), CharTwo.add_self_eq_zero, zero_add]
      _ = _ := by rw [hc edge, ih]; simp [add_comm]

theorem color_eq_distance (u v : Fin n → Option (Fin n)) (hc : Connected u v)
    (i : Fin n) : color u v i = ((endpointGraph u v).dist none (some i) : ZMod 2) := by
  let c := grounded (color u v)
  have prop := (color_eq_cramer _ _ hc).1
  have he {a b} (hab : (endpointGraph u v).Adj a b) : c a + c b = 1 := by
    rcases hab.2 with ⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩
    · exact prop j
    · rw [add_comm]; exact prop j
  obtain ⟨w,hw⟩ := ((graph_connected _ _).mpr hc).exists_walk_length_eq_dist none (some i)
  simpa [c, grounded, hw] using Walk_length_parity c he w

open scoped Sym2

def edgeOf (u v : Fin m → Option (Fin n)) (i : Fin m) := s(u i, v i)

lemma graph_edge_set (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) :
    (endpointGraph u v).edgeSet = Set.range (edgeOf u v) := by
  ext e
  induction e using Sym2.ind with | h p q =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hpq
      rcases hpq.2 with ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩
      · exact ⟨i, rfl⟩
      · exact ⟨i, Sym2.eq_swap⟩
    · rintro ⟨i, hi⟩
      have hh : (u i, v i) = (p,q) ∨ (u i, v i) = (p,q).swap :=
        Sym2.mk_eq_mk_iff.mp hi
      rcases hh with hh | hh
      · obtain ⟨hp,hq⟩ := Prod.mk.inj hh
        exact ⟨hp ▸ hq ▸ hn i, Or.inl ⟨i,hp,hq⟩⟩
      · obtain ⟨hp,hq⟩ := Prod.mk.inj hh
        exact ⟨fun h => hn i (hp.trans (h.symm.trans hq.symm)), Or.inr ⟨i,hp,hq⟩⟩

theorem graph_edge_card (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : Nat.card (endpointGraph u v).edgeSet = m := by
  rw [graph_edge_set _ _ hn, ← Nat.card_congr (Equiv.ofInjective _ hi), Nat.card_fin]

theorem simple_spanning_tree_iff (u v : Fin n → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : (endpointGraph u v).IsTree ↔ Connected u v :=
  graph_isTree_of_card _ _ (graph_edge_card _ _ hn hi)

end Bacher
