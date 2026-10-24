import FiveVertexPositive13C000
import FiveVertexPositive13C001
import FiveVertexPositive13C002
import FiveVertexPositive13C003
import FiveVertexPositive13C004
import FiveVertexPositive13C005
import FiveVertexPositive13C006

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogue : List (List Nat) := [[18,34,34,67,68],[18,34,35,66,68],[18,34,35,67,67],[18,34,36,66,67],[18,34,50,51,68],[18,34,50,52,67],[18,34,51,51,67],[18,34,51,52,66],[18,35,35,66,67],[18,35,36,66,66],[18,35,50,50,68],[18,35,50,51,67],[18,35,50,52,66],[18,35,51,51,66],[18,36,50,50,67],[18,36,50,51,66],[18,50,50,51,52],[18,50,51,51,51],[19,34,34,66,68],[19,34,34,67,67],[19,34,35,66,67],[19,34,36,66,66],[19,34,50,50,68],[19,34,50,51,67],[19,34,50,52,66],[19,34,51,51,66],[19,35,35,66,66],[19,35,50,50,67],[19,35,50,51,66],[19,36,50,50,66],[19,50,50,50,52],[19,50,50,51,51],[20,34,34,66,67],[20,34,35,66,66],[20,34,50,50,67],[20,34,50,51,66],[20,35,50,50,66],[20,50,50,50,51],[33,34,34,52,68],[33,34,35,51,68],[33,34,35,52,67],[33,34,36,50,68],[33,34,36,51,67],[33,34,36,52,66],[33,34,50,52,52],[33,34,51,51,52],[33,35,35,50,68],[33,35,35,51,67],[33,35,35,52,66],[33,35,36,50,67],[33,35,36,51,66],[33,35,50,51,52],[33,35,51,51,51],[33,36,36,50,66],[33,36,50,50,52],[33,36,50,51,51],[34,34,34,51,68],[34,34,34,52,67],[34,34,35,50,68],[34,34,35,51,67],[34,34,35,52,66],[34,34,36,49,68],[34,34,36,50,67],[34,34,36,51,66],[34,34,36,52,65],[34,34,49,52,52],[34,34,50,51,52],[34,34,51,51,51],[34,35,35,49,68],[34,35,35,50,67],[34,35,35,51,66],[34,35,35,52,65],[34,35,36,49,67],[34,35,36,50,66],[34,35,36,51,65],[34,35,49,51,52],[34,35,50,50,52],[34,35,50,51,51],[34,36,36,49,66],[34,36,36,50,65],[34,36,49,50,52],[34,36,49,51,51],[34,36,50,50,51],[35,35,35,49,67],[35,35,35,50,66],[35,35,35,51,65],[35,35,36,49,66],[35,35,36,50,65],[35,35,49,50,52],[35,35,49,51,51],[35,35,50,50,51],[35,36,49,50,51],[35,36,50,50,50],[36,36,49,50,50]]

theorem catalogue_eq : hardProfiles 5 13 2 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 13 2 false) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 2 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact profile45
  · exact profile46
  · exact profile47
  · exact profile48
  · exact profile49
  · exact profile50
  · exact profile51
  · exact profile52
  · exact profile53
  · exact profile54
  · exact profile55
  · exact profile56
  · exact profile57
  · exact profile58
  · exact profile59
  · exact profile60
  · exact profile61
  · exact profile62
  · exact profile63
  · exact profile64
  · exact profile65
  · exact profile66
  · exact profile67
  · exact profile68
  · exact profile69
  · exact profile70
  · exact profile71
  · exact profile72
  · exact profile73
  · exact profile74
  · exact profile75
  · exact profile76
  · exact profile77
  · exact profile78
  · exact profile79
  · exact profile80
  · exact profile81
  · exact profile82
  · exact profile83
  · exact profile84
  · exact profile85
  · exact profile86
  · exact profile87
  · exact profile88
  · exact profile89
  · exact profile90
  · exact profile91
  · exact profile92
  · exact profile93
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 false 5 0 13 13) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 2 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=13)
    (positiveOut : ∀x,1≤SparseSupport.outdegree E x)
    (positiveIn : ∀x,1≤SparseSupport.indegree E x) : score E≤2 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=13 := by
    exact (SparseSupport.arc_rows E).symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=13 := by
    exact (SparseSupport.arc_columns E).symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg (fun x => by have := positiveOut x; have := positiveIn x; omega)
    (fun x => Or.inl ⟨by have := positiveOut x; omega,by have := positiveIn x; omega⟩) td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.FiveVertexPositive13
