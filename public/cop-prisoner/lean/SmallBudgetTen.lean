import SmallBudgetNine
import SmallBudgetTenWitness
import GraphSupport
import SmallBudgetTenFinite5
import SmallBudgetTenFinite6
import SmallBudgetTenFinite7
import SmallBudgetTenFinite8
import SmallBudgetTenFinite9
import SmallBudgetTenFinite10

/-! Sharp ten-arrow upper bound, including arbitrary sources, sinks and
isolated vertices. Degree-one deletions reduce to the verified nine-arrow
bound; the remaining actual support has at most ten vertices. -/
namespace Delivery.SmallBudgetTen
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

theorem support_upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=10) (order : n≤10)
    (degree : ∀x,2≤outdegree E x+indegree E x)
    (regularity : ∀x,(0<outdegree E x ∧ 0<indegree E x) ∨
      (true=true ∧ outdegree E x+indegree E x=2)) : score E≤6 := by
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; rw [budget] at h; omega
  · have h := arcCount_add_missingCount E loops; have q := score_le_missing E; rw [budget] at h; omega
  · exact SmallBudgetTenFinite5.upper E loops budget degree regularity
  · exact SmallBudgetTenFinite6.upper E loops budget degree regularity
  · exact SmallBudgetTenFinite7.upper E loops budget degree regularity
  · exact SmallBudgetTenFinite8.upper E loops budget degree regularity
  · exact SmallBudgetTenFinite9.upper E loops budget degree regularity
  · exact SmallBudgetTenFinite10.upper E loops budget degree regularity

theorem source_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=10) (v : Fin n) (source : ∀x,¬E x v)
    (positive : 0<outdegree E v) (different : outdegree E v≠2) : score E≤6 := by
  have deletion := source_deletion E loops v source
  by_cases one : outdegree E v=1
  · have old := SmallBudgetNine.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := SmallBudgetNine.seven_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem sink_exclusion {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=10) (v : Fin n) (sink : ∀x,¬E v x)
    (positive : 0<indegree E v) (different : indegree E v≠2) : score E≤6 := by
  have deletion := sink_deletion E loops v sink
  by_cases one : indegree E v=1
  · have old := SmallBudgetNine.upper (isolate E v) (isolate_loopless loops v) (by omega)
    have same := deletion.2.2.2 (by omega)
    omega
  · have old := SmallBudgetNine.seven_upper (isolate E v) (isolate_loopless loops v) (by omega)
    omega

theorem upper {n : Nat} (E : Graph (Fin n)) (loops : Loopless E)
    (budget : arcCount E=10) : score E≤6 := by
  by_cases small : score E≤6
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

theorem maximum {n : Nat} (order : 6≤n) : IsMaximum n 10 6 := by
  constructor
  · exact fun E loops budget => upper E loops budget
  · have exactScore : score SmallBudgetTenWitness.edge=6 := by
      have lo := SmallBudgetTenWitness.counted_pairs
      have hi := upper SmallBudgetTenWitness.edge SmallBudgetTenWitness.loopless
        SmallBudgetTenWitness.arrows
      omega
    obtain ⟨F,loops,arcs,value⟩ := GraphPadding.pad_to_order SmallBudgetTenWitness.edge
      SmallBudgetTenWitness.loopless order
    exact ⟨F,loops,arcs.trans SmallBudgetTenWitness.arrows,value.trans exactScore⟩

#print axioms upper
#print axioms maximum
end Delivery.SmallBudgetTen
