import SmallBudgetProfilesFast
import SmallBudgetTenFinite10Profile000Part000
import SmallBudgetTenFinite10Profile001Part000
import SmallBudgetTenFinite10Profile002Part000

namespace Delivery.SmallBudgetTenFinite10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[2,2,2,2,2,32,32,32,32,32],[2,2,2,2,17,17,32,32,32,32],[2,2,2,17,17,17,17,32,32,32]]

theorem catalogue_eq : SmallBudgetProfilesFast.hardProfiles 10 10 6 true=catalogue := by
  unfold SmallBudgetProfilesFast.hardProfiles SmallBudgetProfilesFast.profiles
  have letters : alphabet 10 true=[2,17,18,19,20,21,22,23,24,25,32,33,34,35,36,37,38,39,40,41,49,50,51,52,53,54,55,56,57,65,66,67,68,69,70,71,72,73,81,82,83,84,85,86,87,88,89,97,98,99,100,101,102,103,104,105,113,114,115,116,117,118,119,120,121,129,130,131,132,133,134,135,136,137,145,146,147,148,149,150,151,152,153] := by decide +kernel
  rw [letters]
  decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈SmallBudgetProfilesFast.hardProfiles 10 10 6 true) :
    Upper (n:=10) (D xs.reverse) (R xs.reverse) [] 6 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
theorem profile_upper (xs : List Nat) (member : xs∈SmallBudgetProfilesFast.profiles 10 true 10 0 10 10) :
    Upper (n:=10) (D xs.reverse) (R xs.reverse) [] 6 :=
  SmallBudgetProfilesFast.upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 10)) (loops : Loopless E) (budget : arcCount E=10)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤6 := by
  have od (x) : SparseSupport.outdegree E x<10 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<10 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 10).map (SparseSupport.outdegree E)).sum=10 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 10).map (SparseSupport.indegree E)).sum=10 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := SmallBudgetProfilesFast.sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetTenFinite10
