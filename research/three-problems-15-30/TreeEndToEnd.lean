import TreeAlgorithm
import TreeReindex

namespace Bacher
open scoped BigOperators Classical

/-- The bounded algorithm returns the original vertex partition, expressed using
Mathlib's ordinary spanning subgraphs, tree predicate, and graph distance. -/
theorem endpoint_algorithm {n m : ℕ} (u v : Fin m → Option (Fin n))
    (noLoops : ∀ i, u i ≠ v i) (distinct : Function.Injective (edgeOf u v)) :
    (∀ i, (partitionAlgorithm u v).1 i =
      ∑ H : SimpleGraph (Option (Fin n)), if H ≤ endpointGraph u v ∧ H.IsTree
        then (H.dist none (some i) : ZMod 2) else 0) ∧
    (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨correct,bound⟩ := partitionAlgorithm_spec u v
  exact ⟨fun i => (congrFun correct i).trans (product_as_tree_distance u v noLoops distinct i), bound⟩

/-- The graph representation in `endpoint_algorithm` covers every ordinary graph. -/
theorem every_graph_algorithm {n : ℕ} (G : SimpleGraph (Option (Fin n))) :
    ∃ (m : ℕ) (u v : Fin m → Option (Fin n)), endpointGraph u v = G ∧
      (∀ i, (partitionAlgorithm u v).1 i =
        ∑ H : SimpleGraph (Option (Fin n)), if H ≤ G ∧ H.IsTree
          then (H.dist none (some i) : ZMod 2) else 0) ∧
      (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨m,u,v,hn,hi,rfl⟩ := exists_presentation G
  exact ⟨m,u,v,rfl,endpoint_algorithm u v hn hi⟩

#print axioms endpoint_algorithm
#print axioms every_graph_algorithm
end Bacher
