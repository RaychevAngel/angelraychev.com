import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
5 vertices with 8 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetEightFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e : Nat) : Rows 5 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16]
  | 2 => [3,5,9,17,6,10,18,12,20,24]
  | 3 => [7,11,19,13,21,25,14,22,26,28]
  | 4 => [15,23,27,29,30]
  | 5 => [31]
  | _ => []

theorem cover (d : Fin 6) : RowCover 5 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 7 7 23 27 19), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,5] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,5] 4 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,5] 4 profile0_node2_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 19 7 28 20), lower := (rows 7 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile0_node4 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,3] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,3] 4 profile0_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,3] 4 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 19 21 14 22), lower := (rows 7 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile0_node5 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,17] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,17] 4 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,17] 4 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 19 22 13 21), lower := (rows 7 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 22 22 8 16) }] }

theorem profile0_node6 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,18] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,18] 4 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17,18] 4 profile0_node6_cert).mp (by decide +kernel))

def profile0_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17] 4 := by
  apply routed_branch (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17] 4 (by decide) (choices 2) [3,17,18] profile0_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,17] (choices 2) [3,17,18] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node5
  · exact profile0_node6

def profile0_node7_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 7 22 23 27 19), lower := (rows 7 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile0_node7 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,20] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,20] 4 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6,20] 4 profile0_node7_cert).mp (by decide +kernel))

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6] 4 := by
  apply routed_branch (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6] 4 (by decide) (choices 2) [5,17,20] profile0_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [6] (choices 2) [5,17,20] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node7

def profile0_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 7 7 28 20), lower := (rows 19 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) }] }

theorem profile0_node10 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,3] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,3] 4 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,3] 4 profile0_node10_cert).mp (by decide +kernel))

def profile0_node11_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 7 21 14 22), lower := (rows 19 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) }] }

theorem profile0_node11 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,17] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,17] 4 profile0_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,17] 4 profile0_node11_cert).mp (by decide +kernel))

def profile0_node12_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 7 22 13 21), lower := (rows 19 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 6 22 8 16) }] }

theorem profile0_node12 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,18] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,18] 4 profile0_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5,18] 4 profile0_node12_cert).mp (by decide +kernel))

def profile0_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node9 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5] 4 := by
  apply routed_branch (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5] 4 (by decide) (choices 2) [3,17,18] profile0_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,5] (choices 2) [3,17,18] profile0_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node10
  · exact profile0_node11
  · exact profile0_node12

def profile0_node13_cert : CutBound 5 := { lost := (rows 4 4 0 0 0), upper := (rows 19 19 7 15 23), lower := (rows 19 19 4 8 16), losses := [{ target := 2, region := (rows 19 19 0 8 16), good := (rows 19 19 0 8 19) }] }

theorem profile0_node13 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,17] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,17] 4 profile0_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,17] 4 profile0_node13_cert).mp (by decide +kernel))

def profile0_node14_cert : CutBound 5 := { lost := (rows 4 0 0 0 0), upper := (rows 19 22 7 15 23), lower := (rows 19 22 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 19 19 0 8 16) }] }

theorem profile0_node14 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,20] 4 :=
  cut_bound_sound (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,20] 4 profile0_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18,20] 4 profile0_node14_cert).mp (by decide +kernel))

def profile0_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node8 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18] 4 := by
  apply routed_branch (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18] 4 (by decide) (choices 2) [5,17,20] profile0_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [18] (choices 2) [5,17,20] profile0_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node9
  · exact profile0_node13
  · exact profile0_node14

def profile0_node0_route : Route 5 := (fun mask => match mask with | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [] 4 := by
  apply routed_branch (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [] 4 (by decide) (choices 2) [6,18] profile0_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [] (choices 2) [6,18] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node8

theorem profile0 : Upper (D (n:=5) [34,34,34,32,2]) (R (n:=5) [34,34,34,32,2]) [] 4 := profile0_node0

def catalogue : List (List Nat) := [[2,32,34,34,34]]

theorem catalogue_eq : hardProfiles 5 8 4 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 8 4 true) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 4 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 true 5 0 8 8) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 4 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=8)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤4 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=8 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=8 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetEightFinite5
