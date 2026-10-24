import SmallBudgetSix
import GraphSupport
import SmallBudgetSevenOrder4
import SmallBudgetSevenOrder5
import SmallBudgetSevenOrder6
import SmallBudgetSevenOrder7

/-! Sharp seven-arrow upper bound, including arbitrary sources, sinks and
isolated vertices. Degree-one deletions reduce to the verified six-arrow
bound; the remaining actual support has at most seven vertices. -/
namespace Delivery.SmallBudgetSeven
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem support_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=7) (order : n≤7)
    (degree : ∀x,2≤outdegree E x+indegree E x) : score E≤2 := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · exact SmallBudgetSevenOrder4.upper E loops budget degree
  · exact SmallBudgetSevenOrder5.upper E loops budget degree
  · exact SmallBudgetSevenOrder6.upper E loops budget degree
  · exact SmallBudgetSevenOrder7.upper E loops budget degree

theorem upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=7) : score E≤2 := by
  by_cases small : score E≤2
  · exact small
  · have total (x : Fin n) (inside : GraphSupport.Support E x) :
        2≤outdegree E x+indegree E x := by
      apply Classical.byContradiction
      intro low
      have positive : 0<outdegree E x+indegree E x := by
        rcases inside with h | h
        · have h' : 0<outdegree E x := card_positive.mpr h
          omega
        · have h' : 0<indegree E x := card_positive.mpr h
          omega
      have cases : (outdegree E x=1 ∧ indegree E x=0) ∨
          (outdegree E x=0 ∧ indegree E x=1) := by omega
      rcases cases with ⟨od,idg⟩ | ⟨od,idg⟩
      · have source : ∀y,¬E y x := card_eq_zero.mp idg
        have deletion := source_deletion E loops x source
        have old := SmallBudgetSix.upper (isolate E x) (isolate_loopless loops x) (by omega)
        have preserved := deletion.2.2.2 (by omega)
        omega
      · have sink : ∀y,¬E x y := card_eq_zero.mp od
        have deletion := sink_deletion E loops x sink
        have old := SmallBudgetSix.upper (isolate E x) (isolate_loopless loops x) (by omega)
        have preserved := deletion.2.2.2 (by omega)
        omega
    have order := GraphSupport.order_le_arcs E total
    have arcs := GraphSupport.arcCount_eq E
    have degrees (x : Fin (card (GraphSupport.Support E))) :
        2≤outdegree (GraphSupport.graph E) x+indegree (GraphSupport.graph E) x := by
      rw [GraphSupport.outdegree_eq,GraphSupport.indegree_eq]
      exact total _ (GraphSupport.embed_mem _ _)
    have bound := support_upper (GraphSupport.graph E) (GraphSupport.loopless E loops)
      (arcs.trans budget) (by omega) degrees
    have retained := GraphSupport.score_le E loops
    omega

theorem maximum {n : Nat} (order : 5≤n) : IsMaximum n 7 2 := by
  constructor
  · exact fun E loops budget => upper E loops budget
  · obtain ⟨E,loops,arcs,value⟩ := GraphPadding.add_one_arrow
      ExactScoreCertificates.FourVertex.edge ExactScoreCertificates.FourVertex.loopless 0
    obtain ⟨F,floops,farcs,fvalue⟩ := GraphPadding.pad_to_order E loops order
    refine ⟨F,floops,?_,?_⟩
    · rw [farcs,arcs,ExactScoreCertificates.FourVertex.arcs_six]
    · rw [fvalue,value,ExactScoreCertificates.FourVertex.score_two]

#print axioms upper
#print axioms maximum
end Delivery.SmallBudgetSeven
