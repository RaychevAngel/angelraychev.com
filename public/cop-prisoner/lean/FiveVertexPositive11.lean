import FiveVertexPositive11C000
import FiveVertexPositive11C001
import FiveVertexPositive11C002
import FiveVertexPositive11C003
import FiveVertexPositive11C004

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[18,33,34,34,68],[18,33,34,35,67],[18,33,34,36,66],[18,33,34,50,52],[18,33,34,51,51],[18,33,35,35,66],[18,33,35,50,51],[18,33,36,50,50],[18,34,34,34,67],[18,34,34,35,66],[18,34,34,36,65],[18,34,34,49,52],[18,34,34,50,51],[18,34,35,35,65],[18,34,35,49,51],[18,34,35,50,50],[18,34,36,49,50],[18,35,35,49,50],[19,33,34,34,67],[19,33,34,35,66],[19,33,34,50,51],[19,33,35,50,50],[19,34,34,34,66],[19,34,34,35,65],[19,34,34,49,51],[19,34,34,50,50],[19,34,35,49,50],[20,33,34,34,66],[20,33,34,50,50],[20,34,34,34,65],[20,34,34,49,50],[33,34,34,34,52],[33,34,34,35,51],[33,34,34,36,50],[33,34,35,35,50],[34,34,34,34,51],[34,34,34,35,50],[34,34,34,36,49],[34,34,35,35,49]]

theorem catalogue_eq : hardProfiles 5 11 3 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 11 3 false) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 3 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
  · exact profile4
  · exact profile5
  · exact profile6
  · exact profile7
  · exact profile8
  · exact profile9
  · exact profile10
  · exact profile11
  · exact profile12
  · exact profile13
  · exact profile14
  · exact profile15
  · exact profile16
  · exact profile17
  · exact profile18
  · exact profile19
  · exact profile20
  · exact profile21
  · exact profile22
  · exact profile23
  · exact profile24
  · exact profile25
  · exact profile26
  · exact profile27
  · exact profile28
  · exact profile29
  · exact profile30
  · exact profile31
  · exact profile32
  · exact profile33
  · exact profile34
  · exact profile35
  · exact profile36
  · exact profile37
  · exact profile38
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 false 5 0 11 11) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 3 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=11)
    (positiveOut : ∀x,1≤SparseSupport.outdegree E x)
    (positiveIn : ∀x,1≤SparseSupport.indegree E x) : score E≤3 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=11 := by
    exact (SparseSupport.arc_rows E).symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=11 := by
    exact (SparseSupport.arc_columns E).symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg (fun x => by have := positiveOut x; have := positiveIn x; omega)
    (fun x => Or.inl ⟨by have := positiveOut x; omega,by have := positiveIn x; omega⟩) td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.FiveVertexPositive11
