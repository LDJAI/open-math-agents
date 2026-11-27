import TreeAlgorithm
import TreeReindex

namespace Bacher
open scoped Classical
variable {n m : ℕ}

/-- Correct on every simple, loopless graph presented by its indexed edge list.
No assumption on the parity of its spanning-tree count is needed. -/
theorem algorithm_on_graph (u v : Fin m → Option (Fin n))
    (hn : ∀ j, u j ≠ v j) (hi : Function.Injective (edgeOf u v)) (i : Fin n) :
    (partitionAlgorithm u v).1 i = ∑ H : SimpleGraph (Option (Fin n)),
      if H ≤ endpointGraph u v ∧ H.IsTree then (H.dist none (some i) : ZMod 2) else 0 := by
  rw [(partitionAlgorithm_spec u v).1]
  exact product_as_tree_distance u v hn hi i

end Bacher
