import SmallBudgetEight
import SmallBudgetNineWitness
import GraphSupport
import SmallBudgetNineFinite5
import SmallBudgetNineFinite6
import SmallBudgetNineFinite7
import SmallBudgetNineFinite8
import SmallBudgetNineFinite9

/-! Sharp nine-arrow upper bound, including arbitrary sources, sinks and
isolated vertices. Degree-one deletions reduce to the verified eight-arrow
bound; the remaining actual support has at most nine vertices. -/
namespace Delivery.SmallBudgetNine
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem support_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=9) (order : n≤9)
    (degree : ∀x,2≤outdegree E x+indegree E x)
    (regularity : ∀x,(0<outdegree E x ∧ 0<indegree E x) ∨
      (false=true ∧ outdegree E x+indegree E x=2)) : score E≤5 := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; have q := score_le_missing E; rw [budget] at h; omega
  · exact SmallBudgetNineFinite5.upper E loops budget degree regularity
  · exact SmallBudgetNineFinite6.upper E loops budget degree regularity
  · exact SmallBudgetNineFinite7.upper E loops budget degree regularity
  · exact SmallBudgetNineFinite8.upper E loops budget degree regularity
  · exact SmallBudgetNineFinite9.upper E loops budget degree regularity

theorem seven_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E≤7) : score E≤2 := by
  by_cases small : arcCount E≤5
  · have h := SmallBudgetEight.five_upper E loops small; omega
  · by_cases six : arcCount E=6
    · exact SmallBudgetSix.upper E loops six
    · exact SmallBudgetSeven.upper E loops (by omega)

theorem source_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=9) (v : Fin n) (source : ∀x,¬E x v)
    (positive : 0<outdegree E v) : score E≤5 := by
  have deletion := source_deletion E loops v source
  by_cases one : outdegree E v=1
  · have old := SmallBudgetEight.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := seven_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem sink_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=9) (v : Fin n) (sink : ∀x,¬E v x)
    (positive : 0<indegree E v) : score E≤5 := by
  have deletion := sink_deletion E loops v sink
  by_cases one : indegree E v=1
  · have old := SmallBudgetEight.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := seven_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=9) : score E≤5 := by
  by_cases small : score E≤5
  · exact small
  · have positive (x : Fin n) (inside : GraphSupport.Support E x) :
        0<outdegree E x ∧ 0<indegree E x := by
      have incident : 0<outdegree E x+indegree E x := by
        rcases inside with h | h
        · have h' : 0<outdegree E x := card_positive.mpr h; omega
        · have h' : 0<indegree E x := card_positive.mpr h; omega
      by_cases hin : indegree E x=0
      · exact False.elim (small (source_exclusion E loops budget x (card_eq_zero.mp hin) (by omega)))
      · by_cases hout : outdegree E x=0
        · exact False.elim (small (sink_exclusion E loops budget x (card_eq_zero.mp hout) (by omega)))
        · exact ⟨by omega,by omega⟩
    have total (x) (inside : GraphSupport.Support E x) : 2≤outdegree E x+indegree E x := by
      have h := positive x inside; omega
    have order := GraphSupport.order_le_arcs E total
    have arcs := GraphSupport.arcCount_eq E
    have degrees (x : Fin (card (GraphSupport.Support E))) :
        2≤outdegree (GraphSupport.graph E) x+indegree (GraphSupport.graph E) x := by
      rw [GraphSupport.outdegree_eq,GraphSupport.indegree_eq]
      exact total _ (GraphSupport.embed_mem _ _)
    have good (x : Fin (card (GraphSupport.Support E))) :
        (0<outdegree (GraphSupport.graph E) x ∧ 0<indegree (GraphSupport.graph E) x) ∨
        (false=true ∧ outdegree (GraphSupport.graph E) x+indegree (GraphSupport.graph E) x=2) := by
      rw [GraphSupport.outdegree_eq,GraphSupport.indegree_eq]
      exact Or.inl (positive _ (GraphSupport.embed_mem _ _))
    have bound := support_upper (GraphSupport.graph E) (GraphSupport.loopless E loops)
      (arcs.trans budget) (by omega) degrees good
    have retained := GraphSupport.score_le E loops
    omega

theorem maximum {n : Nat} (order : 6≤n) : IsMaximum n 9 5 := by
  constructor
  · exact fun E loops budget => upper E loops budget
  · have exactScore : score SmallBudgetNineWitness.edge=5 := by
      have lo := SmallBudgetNineWitness.five_pairs
      have hi := upper SmallBudgetNineWitness.edge SmallBudgetNineWitness.loopless
        SmallBudgetNineWitness.arrows
      omega
    obtain ⟨F,loops,arcs,value⟩ := GraphPadding.pad_to_order SmallBudgetNineWitness.edge
      SmallBudgetNineWitness.loopless order
    exact ⟨F,loops,arcs.trans SmallBudgetNineWitness.arrows,value.trans exactScore⟩

#print axioms upper
#print axioms maximum
end Delivery.SmallBudgetNine
