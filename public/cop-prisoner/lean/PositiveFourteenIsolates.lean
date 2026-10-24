import PositiveFourteen
import GraphSupport

/-! The positive-support fourteen-arrow upper bound allows arbitrary isolated
vertices in the host. Sources, sinks, and support orders below nine remain
outside this statement. -/
namespace Delivery.PositiveFourteenIsolates
open FiniteGame Extremal DenseCombinatorics SparseSupport

theorem upper {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (budget : arcCount E=14) (order : 9≤card (GraphSupport.Support E))
    (positive : ∀ x, GraphSupport.Support E x →
      1≤outdegree E x ∧ 1≤indegree E x) : score E≤13 := by
  have outgoing (x : Fin (card (GraphSupport.Support E))) :
      1≤outdegree (GraphSupport.graph E) x := by
    rw [GraphSupport.outdegree_eq]
    exact (positive _ (GraphSupport.embed_mem _ _)).1
  have incoming (x : Fin (card (GraphSupport.Support E))) :
      1≤indegree (GraphSupport.graph E) x := by
    rw [GraphSupport.indegree_eq]
    exact (positive _ (GraphSupport.embed_mem _ _)).2
  have bound := PositiveFourteen.upper order (GraphSupport.graph E)
    (GraphSupport.loopless E loopless) ((GraphSupport.arcCount_eq E).trans budget)
    outgoing incoming
  exact Nat.le_trans (GraphSupport.score_le E loopless) bound

#print axioms upper
end Delivery.PositiveFourteenIsolates
