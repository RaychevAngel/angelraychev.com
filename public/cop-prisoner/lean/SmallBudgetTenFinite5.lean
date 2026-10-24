import SmallBudgetTenFinite5Profile000Part000
import SmallBudgetTenFinite5Profile001Part000
import SmallBudgetTenFinite5Profile002Part000

namespace Delivery.SmallBudgetTenFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[18,34,34,34,50],[33,34,34,34,35],[34,34,34,34,34]]

theorem catalogue_eq : hardProfiles 5 10 6 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 10 6 true) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 6 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 true 5 0 10 10) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 6 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=10)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤6 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=10 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=10 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetTenFinite5
