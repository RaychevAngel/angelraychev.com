import SmallBudgetSeven
import SmallBudgetEightWitness
import GraphSupport
import SmallBudgetEightFinite5
import SmallBudgetEightFinite6
import SmallBudgetEightFinite7
import SmallBudgetEightFinite8

/-! Sharp eight-arrow upper bound, including arbitrary sources, sinks and
isolated vertices. Degree-one deletions reduce to the verified seven-arrow
bound; the remaining actual support has at most eight vertices. -/
namespace Delivery.SmallBudgetEight
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem support_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=8) (order : n≤8)
    (degree : ∀x,2≤outdegree E x+indegree E x)
    (regularity : ∀x,(0<outdegree E x ∧ 0<indegree E x) ∨
      (true=true ∧ outdegree E x+indegree E x=2)) : score E≤4 := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; have q := score_le_missing E; rw [budget] at h; omega
  · exact SmallBudgetEightFinite5.upper E loops budget degree regularity
  · exact SmallBudgetEightFinite6.upper E loops budget degree regularity
  · exact SmallBudgetEightFinite7.upper E loops budget degree regularity
  · exact SmallBudgetEightFinite8.upper E loops budget degree regularity

theorem five_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E≤5) : score E≤1 := by
  have h := SparseParity.upper E loops
  have cases : arcCount E=0 ∨ arcCount E=1 ∨ arcCount E=2 ∨ arcCount E=3 ∨
      arcCount E=4 ∨ arcCount E=5 := by omega
  rcases cases with h0 | h0 | h0 | h0 | h0 | h0 <;>
    simp [h0,SparseParity.budgetBound] at h <;> omega

theorem source_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=8) (v : Fin n) (source : ∀x,¬E x v)
    (positive : 0<outdegree E v) (different : outdegree E v≠2) : score E≤4 := by
  have deletion := source_deletion E loops v source
  by_cases one : outdegree E v=1
  · have old := SmallBudgetSeven.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := five_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem sink_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=8) (v : Fin n) (sink : ∀x,¬E v x)
    (positive : 0<indegree E v) (different : indegree E v≠2) : score E≤4 := by
  have deletion := sink_deletion E loops v sink
  by_cases one : indegree E v=1
  · have old := SmallBudgetSeven.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := five_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=8) : score E≤4 := by
  by_cases small : score E≤4
  · exact small
  · have regularity (x : Fin n) (inside : GraphSupport.Support E x) :
        (0<outdegree E x ∧ 0<indegree E x) ∨ outdegree E x+indegree E x=2 := by
      have positive : 0<outdegree E x+indegree E x := by
        rcases inside with h | h
        · have h' : 0<outdegree E x := card_positive.mpr h; omega
        · have h' : 0<indegree E x := card_positive.mpr h; omega
      by_cases hin : indegree E x=0
      · by_cases two : outdegree E x=2
        · exact Or.inr (by omega)
        · exact False.elim (small (source_exclusion E loops budget x (card_eq_zero.mp hin) (by omega) two))
      · by_cases hout : outdegree E x=0
        · by_cases two : indegree E x=2
          · exact Or.inr (by omega)
          · exact False.elim (small (sink_exclusion E loops budget x (card_eq_zero.mp hout) (by omega) two))
        · exact Or.inl ⟨by omega,by omega⟩
    have total (x) (inside : GraphSupport.Support E x) : 2≤outdegree E x+indegree E x := by
      rcases regularity x inside with h | h <;> omega
    have order := GraphSupport.order_le_arcs E total
    have arcs := GraphSupport.arcCount_eq E
    have degrees (x : Fin (card (GraphSupport.Support E))) :
        2≤outdegree (GraphSupport.graph E) x+indegree (GraphSupport.graph E) x := by
      rw [GraphSupport.outdegree_eq,GraphSupport.indegree_eq]
      exact total _ (GraphSupport.embed_mem _ _)
    have good (x : Fin (card (GraphSupport.Support E))) :
        (0<outdegree (GraphSupport.graph E) x ∧ 0<indegree (GraphSupport.graph E) x) ∨
        (true=true ∧ outdegree (GraphSupport.graph E) x+indegree (GraphSupport.graph E) x=2) := by
      rw [GraphSupport.outdegree_eq,GraphSupport.indegree_eq]
      simpa using regularity _ (GraphSupport.embed_mem _ _)
    have bound := support_upper (GraphSupport.graph E) (GraphSupport.loopless E loops)
      (arcs.trans budget) (by omega) degrees good
    have retained := GraphSupport.score_le E loops
    omega

theorem maximum {n : Nat} (order : 6≤n) : IsMaximum n 8 4 := by
  constructor
  · exact fun E loops budget => upper E loops budget
  · have exactScore : score SmallBudgetEightWitness.edge=4 := by
      have lo := SmallBudgetEightWitness.four_pairs
      have hi := upper SmallBudgetEightWitness.edge SmallBudgetEightWitness.loopless
        SmallBudgetEightWitness.arrows
      omega
    obtain ⟨F,loops,arcs,value⟩ := GraphPadding.pad_to_order SmallBudgetEightWitness.edge
      SmallBudgetEightWitness.loopless order
    exact ⟨F,loops,arcs.trans SmallBudgetEightWitness.arrows,value.trans exactScore⟩

#print axioms upper
#print axioms maximum
end Delivery.SmallBudgetEight
