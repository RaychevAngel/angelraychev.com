import SmallBudgetProfilesFast
import SmallBudgetTenFinite7Profile000Part000
import SmallBudgetTenFinite7Profile001Part000
import SmallBudgetTenFinite7Profile002Part000
import SmallBudgetTenFinite7Profile003Part000
import SmallBudgetTenFinite7Profile004Part000
import SmallBudgetTenFinite7Profile005Part000
import SmallBudgetTenFinite7Profile006Part000
import SmallBudgetTenFinite7Profile007Part000
import SmallBudgetTenFinite7Profile008Part000
import SmallBudgetTenFinite7Profile009Part000
import SmallBudgetTenFinite7Profile010Part000
import SmallBudgetTenFinite7Profile011Part000
import SmallBudgetTenFinite7Profile012Part000
import SmallBudgetTenFinite7Profile013Part000
import SmallBudgetTenFinite7Profile014Part000
import SmallBudgetTenFinite7Profile015Part000
import SmallBudgetTenFinite7Profile016Part000
import SmallBudgetTenFinite7Profile017Part000
import SmallBudgetTenFinite7Profile018Part000
import SmallBudgetTenFinite7Profile019Part000
import SmallBudgetTenFinite7Profile020Part000
import SmallBudgetTenFinite7Profile021Part001
import SmallBudgetTenFinite7Profile022Part000
import SmallBudgetTenFinite7Profile023Part000
import SmallBudgetTenFinite7Profile024Part000
import SmallBudgetTenFinite7Profile025Part003
import SmallBudgetTenFinite7Profile026Part002
import SmallBudgetTenFinite7Profile027Part000
import SmallBudgetTenFinite7Profile028Part000
import SmallBudgetTenFinite7Profile029Part000
import SmallBudgetTenFinite7Profile030Part000
import SmallBudgetTenFinite7Profile031Part000
import SmallBudgetTenFinite7Profile032Part000
import SmallBudgetTenFinite7Profile033Part002
import SmallBudgetTenFinite7Profile034Part003
import SmallBudgetTenFinite7Profile035Part000
import SmallBudgetTenFinite7Profile036Part000
import SmallBudgetTenFinite7Profile037Part000
import SmallBudgetTenFinite7Profile038Part000
import SmallBudgetTenFinite7Profile039Part000
import SmallBudgetTenFinite7Profile040Part001
import SmallBudgetTenFinite7Profile041Part001
import SmallBudgetTenFinite7Profile042Part000
import SmallBudgetTenFinite7Profile043Part000
import SmallBudgetTenFinite7Profile044Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[2,2,2,32,32,34,66],[2,2,2,32,32,50,50],[2,2,2,32,33,33,66],[2,2,2,32,33,34,65],[2,2,2,32,33,49,50],[2,2,2,32,34,49,49],[2,2,17,32,33,34,50],[2,2,17,32,34,34,49],[2,2,18,32,32,33,51],[2,2,18,32,32,34,50],[2,2,18,32,32,35,49],[2,2,18,32,33,33,50],[2,2,18,32,33,34,49],[2,2,18,33,33,33,49],[2,2,19,32,32,33,50],[2,2,19,32,32,34,49],[2,2,32,32,32,34,36],[2,2,32,32,32,35,35],[2,2,32,32,33,34,35],[2,2,32,32,34,34,34],[2,2,32,33,33,33,35],[2,2,32,33,33,34,34],[2,2,33,33,33,33,34],[2,17,17,32,34,34,34],[2,17,18,32,32,34,35],[2,17,18,32,33,34,34],[2,17,18,33,33,33,34],[2,17,19,32,32,34,34],[2,18,18,18,32,32,50],[2,18,18,18,32,33,49],[2,18,18,32,32,32,36],[2,18,18,32,32,33,35],[2,18,18,32,32,34,34],[2,18,18,32,33,33,34],[2,18,18,33,33,33,33],[2,18,19,32,32,32,35],[2,18,19,32,32,33,34],[2,18,19,32,33,33,33],[2,18,20,32,32,32,34],[2,19,19,32,32,32,34],[17,18,18,18,32,33,34],[17,18,18,18,33,33,33],[18,18,18,18,32,32,34],[18,18,18,18,32,33,33],[18,18,18,19,32,32,33]]

theorem catalogue_eq : SmallBudgetProfilesFast.hardProfiles 7 10 6 true=catalogue := by
  unfold SmallBudgetProfilesFast.hardProfiles SmallBudgetProfilesFast.profiles
  have letters : alphabet 7 true=[2,17,18,19,20,21,22,32,33,34,35,36,37,38,49,50,51,52,53,54,65,66,67,68,69,70,81,82,83,84,85,86,97,98,99,100,101,102] := by decide +kernel
  rw [letters]
  decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈SmallBudgetProfilesFast.hardProfiles 7 10 6 true) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 6 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact profile39
  · exact profile40
  · exact profile41
  · exact profile42
  · exact profile43
  · exact profile44
theorem profile_upper (xs : List Nat) (member : xs∈SmallBudgetProfilesFast.profiles 7 true 7 0 10 10) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 6 :=
  SmallBudgetProfilesFast.upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 7)) (loops : Loopless E) (budget : arcCount E=10)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤6 := by
  have od (x) : SparseSupport.outdegree E x<7 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<7 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 7).map (SparseSupport.outdegree E)).sum=10 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 7).map (SparseSupport.indegree E)).sum=10 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := SmallBudgetProfilesFast.sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetTenFinite7
