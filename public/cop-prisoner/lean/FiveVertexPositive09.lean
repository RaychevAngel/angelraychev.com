import FiveVertexPositive09C000
import FiveVertexPositive09C001

namespace Delivery.FiveVertexPositive09
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[17,34,34,34,34],[18,18,33,34,50],[18,18,34,34,49],[18,33,33,34,35],[18,33,34,34,34],[19,33,33,34,34]]

theorem catalogue_eq : hardProfiles 5 9 3 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 9 3 false) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 3 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
  · exact profile4
  · exact profile5
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 false 5 0 9 9) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 3 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=9)
    (positiveOut : ∀x,1≤SparseSupport.outdegree E x)
    (positiveIn : ∀x,1≤SparseSupport.indegree E x) : score E≤3 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=9 := by
    exact (SparseSupport.arc_rows E).symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=9 := by
    exact (SparseSupport.arc_columns E).symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg (fun x => by have := positiveOut x; have := positiveIn x; omega)
    (fun x => Or.inl ⟨by have := positiveOut x; omega,by have := positiveIn x; omega⟩) td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.FiveVertexPositive09
