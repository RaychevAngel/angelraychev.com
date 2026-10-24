import SmallBudgetTenFinite6Profile000Part000
import SmallBudgetTenFinite6Profile001Part000
import SmallBudgetTenFinite6Profile002Part000
import SmallBudgetTenFinite6Profile003Part000
import SmallBudgetTenFinite6Profile004Part000
import SmallBudgetTenFinite6Profile005Part000
import SmallBudgetTenFinite6Profile006Part000
import SmallBudgetTenFinite6Profile007Part000
import SmallBudgetTenFinite6Profile008Part000
import SmallBudgetTenFinite6Profile009Part001
import SmallBudgetTenFinite6Profile010Part003
import SmallBudgetTenFinite6Profile011Part000
import SmallBudgetTenFinite6Profile012Part000
import SmallBudgetTenFinite6Profile013Part002
import SmallBudgetTenFinite6Profile014Part001

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[2,2,32,34,34,66],[2,2,32,34,50,50],[2,18,32,34,34,50],[2,18,33,33,34,50],[2,18,33,34,34,49],[2,32,32,34,34,36],[2,32,32,34,35,35],[2,32,33,34,34,35],[2,32,34,34,34,34],[2,33,33,34,34,34],[17,18,33,34,34,34],[18,18,32,33,34,35],[18,18,32,34,34,34],[18,18,33,33,34,34],[18,19,32,33,34,34]]

theorem catalogue_eq : hardProfiles 6 10 6 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 6 10 6 true) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 6 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
theorem profile_upper (xs : List Nat) (member : xs∈profiles 6 true 6 0 10 10) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 6 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 6)) (loops : Loopless E) (budget : arcCount E=10)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤6 := by
  have od (x) : SparseSupport.outdegree E x<6 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<6 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 6).map (SparseSupport.outdegree E)).sum=10 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 6).map (SparseSupport.indegree E)).sum=10 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetTenFinite6
