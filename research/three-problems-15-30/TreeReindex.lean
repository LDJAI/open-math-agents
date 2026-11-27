import TreeGraph
import Mathlib.Data.Finset.Preimage

namespace Bacher
variable {n m : ℕ}
open scoped BigOperators Sym2 Classical

def selectedGraph (u v : Fin m → Option (Fin n)) (s : Selection n m) :=
  endpointGraph (u ∘ edgeAt s) (v ∘ edgeAt s)

lemma selected_edges (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) (s : Selection n m) :
    (selectedGraph u v s).edgeSet = edgeOf u v '' (s.1 : Set (Fin m)) := by
  rw [selectedGraph, graph_edge_set (u ∘ edgeAt s) (v ∘ edgeAt s) (fun j => hn (edgeAt s j))]
  change Set.range (edgeOf u v ∘ edgeAt s) = _
  rw [Set.range_comp]
  change (edgeOf u v) '' (Set.range (s.1.orderEmbOfFin s.2)) = _
  rw [Finset.range_orderEmbOfFin]

lemma selected_injective (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : Function.Injective (selectedGraph u v) := by
  intro s t h
  have hh := congrArg SimpleGraph.edgeSet h
  rw [selected_edges _ _ hn, selected_edges _ _ hn] at hh
  exact Subtype.ext (Finset.coe_injective (Set.image_injective.mpr hi hh))

lemma selected_tree (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (s : Selection n m) :
    (selectedGraph u v s).IsTree ↔ Connected (u ∘ edgeAt s) (v ∘ edgeAt s) := by
  apply simple_spanning_tree_iff _ _ (fun _ => hn _)
  exact hi.comp (s.1.orderEmbOfFin s.2).injective

lemma selected_le (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) (s : Selection n m) :
    selectedGraph u v s ≤ endpointGraph u v := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet,selected_edges _ _ hn,graph_edge_set _ _ hn]
  exact Set.image_subset_range _ _

lemma select_tree (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (H : SimpleGraph (Option (Fin n)))
    (hle : H ≤ endpointGraph u v) (ht : H.IsTree) :
    ∃ s : Selection n m, selectedGraph u v s = H := by
  classical
  let f := edgeOf u v
  have hsub : (H.edgeFinset : Set _) ⊆ Set.range f := by
    rw [SimpleGraph.coe_edgeFinset, ← graph_edge_set u v hn]
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hle
  have him : (H.edgeFinset.preimage f hi.injOn).image f = H.edgeFinset := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.mpr hsub
  let S := H.edgeFinset.preimage f hi.injOn
  have hcard : S.card = n := by
    rw [← Finset.card_image_of_injective _ hi]
    change ((H.edgeFinset.preimage f hi.injOn).image f).card = _
    rw [him]
    have := ht.card_edgeFinset
    simpa using this
  refine ⟨⟨S,hcard⟩, ?_⟩
  apply SimpleGraph.edgeSet_injective
  rw [selected_edges _ _ hn, ← SimpleGraph.coe_edgeFinset, ← him, Finset.coe_image]

/-- The sum in the determinant theorem counts each actual spanning subgraph tree exactly once. -/
theorem product_as_tree_distance (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (i : Fin n) :
    productBit u v i = ∑ H : SimpleGraph (Option (Fin n)),
      if H ≤ endpointGraph u v ∧ H.IsTree then (H.dist none (some i) : ZMod 2) else 0 := by
  classical
  rw [productBit]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun s _ => selectedGraph u v s)
  · intro s hs
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hs ⊢
    exact ⟨selected_le _ _ hn s, (selected_tree _ _ hn hi s).mpr hs⟩
  · intro s _ t _ h
    exact selected_injective _ _ hn hi h
  · intro H hH
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hH
    obtain ⟨s,rfl⟩ := select_tree _ _ hn hi H hH.1 hH.2
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (selected_tree _ _ hn hi s).mp hH.2⟩, rfl⟩
  · intro s hs
    exact color_eq_distance _ _ (Finset.mem_filter.mp hs).2 i

/-- Every ordinary finite simple graph admits an indexed, unduplicated edge presentation. -/
theorem exists_presentation (G : SimpleGraph (Option (Fin n))) :
    ∃ (m : ℕ) (u v : Fin m → Option (Fin n)), (∀ j, u j ≠ v j) ∧
      Function.Injective (edgeOf u v) ∧ endpointGraph u v = G := by
  classical
  let e := (Fintype.equivFin G.edgeSet).symm
  let f := fun i => (e i).val
  let u := fun i => (f i).out.1
  let v := fun i => (f i).out.2
  have hf (i) : edgeOf u v i = f i := by
    change Quot.mk _ (f i).out = f i
    exact Quot.out_eq _
  have hn (i) : u i ≠ v i := by
    intro he
    have hd : (edgeOf u v i).IsDiag := Sym2.mk_isDiag_iff.mpr he
    rw [hf] at hd
    exact G.not_isDiag_of_mem_edgeSet (e i).property hd
  have hi : Function.Injective (edgeOf u v) := by
    intro i j h
    apply e.injective
    exact Subtype.ext ((hf i).symm.trans (h.trans (hf j)))
  refine ⟨_,u,v,hn,hi,SimpleGraph.edgeSet_injective ?_⟩
  rw [graph_edge_set _ _ hn]
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    rw [hf]; exact (e j).property
  · intro hz
    obtain ⟨i,hi⟩ := e.surjective ⟨z,hz⟩
    exact ⟨i,(hf i).trans (congrArg Subtype.val hi)⟩

end Bacher
