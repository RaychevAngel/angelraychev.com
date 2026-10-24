import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
5 vertices with 9 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetNineFinite5
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

def profile0_node2_cert : CutBound 5 := { lost := (rows 16 16 0 4 0), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 7 7 7 8 0) }] }

theorem profile0_node2 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 5 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 5 profile0_node2_cert).mp (by decide +kernel))

def profile0_node5_cert : Bound 5 := { allowed := (rows 16 20 2 4 0), upper := (rows 7 11 21 26 20), lower := (rows 7 11 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) }] }

theorem profile0_node5 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 5 profile0_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 5 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : Bound 5 := { allowed := (rows 16 20 2 2 0), upper := (rows 7 11 21 28 18), lower := (rows 7 11 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) }] }

theorem profile0_node6 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 5 profile0_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 5 profile0_node6_cert).mp (by decide +kernel))

def profile0_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node4 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] 5 (by decide) (choices 2) [18,20] profile0_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] (choices 2) [18,20] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node5
  · exact profile0_node6

def profile0_node7_cert : CutBound 5 := { lost := (rows 16 0 0 2 0), upper := (rows 7 11 22 29 21), lower := (rows 7 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 7 11 7 8 0) }] }

theorem profile0_node7 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] 5 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] 5 profile0_node7_cert).mp (by decide +kernel))

def profile0_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] 5 (by decide) (choices 2) [17,18] profile0_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] (choices 2) [17,18] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node4
  · exact profile0_node7

def profile0_node8_cert : CutBound 5 := { lost := (rows 16 0 0 4 0), upper := (rows 7 14 23 27 19), lower := (rows 7 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 7 15 4 8 0) }] }

theorem profile0_node8 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] 5 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] 5 profile0_node8_cert).mp (by decide +kernel))

def profile0_node10_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 7 19 7 28 28), lower := (rows 7 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile0_node10 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 5 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 5 profile0_node10_cert).mp (by decide +kernel))

def profile0_node12_cert : Bound 5 := { allowed := (rows 16 4 18 4 0), upper := (rows 7 19 13 26 20), lower := (rows 7 19 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) }] }

theorem profile0_node12 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 5 profile0_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 5 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : Bound 5 := { allowed := (rows 16 4 18 2 0), upper := (rows 7 19 13 28 18), lower := (rows 7 19 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) }] }

theorem profile0_node13 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 5 profile0_node13_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 5 profile0_node13_cert).mp (by decide +kernel))

def profile0_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node11 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] 5 (by decide) (choices 2) [18,20] profile0_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] (choices 2) [18,20] profile0_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node12
  · exact profile0_node13

def profile0_node14_cert : CutBound 5 := { lost := (rows 16 0 0 2 0), upper := (rows 7 19 14 29 21), lower := (rows 7 19 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 7 3 15 8 0) }] }

theorem profile0_node14 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] 5 profile0_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] 5 profile0_node14_cert).mp (by decide +kernel))

def profile0_node15_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 7 19 21 14 30), lower := (rows 7 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 21 21 8 16) }] }

theorem profile0_node15 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 5 profile0_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 5 profile0_node15_cert).mp (by decide +kernel))

def profile0_node16_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 7 19 22 13 29), lower := (rows 7 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile0_node16 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 5 profile0_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 5 profile0_node16_cert).mp (by decide +kernel))

def profile0_node18_cert : Bound 5 := { allowed := (rows 16 4 2 20 0), upper := (rows 7 19 28 11 20), lower := (rows 7 19 28 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 29), good := (rows 22 18 28 30 16) }] }

theorem profile0_node18 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 5 profile0_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 5 profile0_node18_cert).mp (by decide +kernel))

def profile0_node19_cert : Bound 5 := { allowed := (rows 16 4 2 18 0), upper := (rows 7 19 28 13 18), lower := (rows 7 19 28 13 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 22 18 28 28 16) }] }

theorem profile0_node19 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 5 profile0_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 5 profile0_node19_cert).mp (by decide +kernel))

def profile0_node20_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 7 19 28 14 17), lower := (rows 7 19 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) }] }

theorem profile0_node20 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 5 profile0_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 5 profile0_node20_cert).mp (by decide +kernel))

def profile0_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node17 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] 5 (by decide) (choices 2) [3,5,6] profile0_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] (choices 2) [3,5,6] profile0_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node18
  · exact profile0_node19
  · exact profile0_node20

def profile0_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node9 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] 5 (by decide) (choices 2) [3,9,10,17,18,24] profile0_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] (choices 2) [3,9,10,17,18,24] profile0_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node10
  · exact profile0_node11
  · exact profile0_node14
  · exact profile0_node15
  · exact profile0_node16
  · exact profile0_node17

def profile0_node21_cert : CutBound 5 := { lost := (rows 16 0 0 4 0), upper := (rows 7 22 31 27 27), lower := (rows 7 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 7 7 4 8 0) }] }

theorem profile0_node21 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] 5 profile0_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] 5 profile0_node21_cert).mp (by decide +kernel))

def profile0_node23_cert : CutBound 5 := { lost := (rows 16 0 16 2 0), upper := (rows 7 26 7 29 21), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile0_node23 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 5 profile0_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 5 profile0_node23_cert).mp (by decide +kernel))

def profile0_node25_cert : Bound 5 := { allowed := (rows 16 4 2 20 0), upper := (rows 7 26 21 11 20), lower := (rows 7 26 21 11 16), losses := [{ target := 0, region := (rows 0 10 4 8 21), good := (rows 22 26 20 26 16) }] }

theorem profile0_node25 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 5 profile0_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 5 profile0_node25_cert).mp (by decide +kernel))

def profile0_node26_cert : Bound 5 := { allowed := (rows 16 4 2 18 0), upper := (rows 7 26 21 13 18), lower := (rows 7 26 21 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 27), good := (rows 22 26 20 30 16) }] }

theorem profile0_node26 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 5 profile0_node26_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 5 profile0_node26_cert).mp (by decide +kernel))

def profile0_node27_cert : CutBound 5 := { lost := (rows 0 1 0 1 0), upper := (rows 7 26 21 14 17), lower := (rows 7 26 21 14 16), losses := [{ target := 0, region := (rows 0 6 4 13 16), good := (rows 14 26 30 14 16) }] }

theorem profile0_node27 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 5 profile0_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 5 profile0_node27_cert).mp (by decide +kernel))

def profile0_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node24 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] 5 (by decide) (choices 2) [3,5,6] profile0_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] (choices 2) [3,5,6] profile0_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node25
  · exact profile0_node26
  · exact profile0_node27

def profile0_node28_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 7 26 22 13 21), lower := (rows 7 26 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 20 8 16) }] }

theorem profile0_node28 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 5 profile0_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 5 profile0_node28_cert).mp (by decide +kernel))

def profile0_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node22 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] 5 (by decide) (choices 2) [3,17,18] profile0_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] (choices 2) [3,17,18] profile0_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node23
  · exact profile0_node24
  · exact profile0_node28

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] 5 (by decide) (choices 2) [5,9,12,17,20,24] profile0_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] (choices 2) [5,9,12,17,20,24] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node8
  · exact profile0_node9
  · exact profile0_node21
  · exact profile0_node22

def profile0_node31_cert : CutBound 5 := { lost := (rows 0 16 0 1 0), upper := (rows 11 7 21 30 22), lower := (rows 11 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 11 7 7 8 0) }] }

theorem profile0_node31 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] 5 profile0_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] 5 profile0_node31_cert).mp (by decide +kernel))

def profile0_node33_cert : Bound 5 := { allowed := (rows 20 16 0 6 0), upper := (rows 11 7 22 25 20), lower := (rows 11 7 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 22 22 28 16) }] }

theorem profile0_node33 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 5 profile0_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 5 profile0_node33_cert).mp (by decide +kernel))

def profile0_node34_cert : Bound 5 := { allowed := (rows 20 16 1 2 0), upper := (rows 11 7 22 28 17), lower := (rows 11 7 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 10 14 30 28 16) }] }

theorem profile0_node34 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 5 profile0_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 5 profile0_node34_cert).mp (by decide +kernel))

def profile0_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node32 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] 5 (by decide) (choices 2) [17,20] profile0_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] (choices 2) [17,20] profile0_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node33
  · exact profile0_node34

def profile0_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node30 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] 5 (by decide) (choices 2) [17,18] profile0_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] (choices 2) [17,18] profile0_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node31
  · exact profile0_node32

def profile0_node36_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 11 19 7 28 20), lower := (rows 11 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 10 18 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 9 17 29 8 16) }] }

theorem profile0_node36 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 5 profile0_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 5 profile0_node36_cert).mp (by decide +kernel))

def profile0_node37_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 11 19 21 14 22), lower := (rows 11 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 19 19 8 16) }] }

theorem profile0_node37 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] 5 profile0_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] 5 profile0_node37_cert).mp (by decide +kernel))

def profile0_node38_cert : CutBound 5 := { lost := (rows 16 0 1 16 0), upper := (rows 11 19 22 13 21), lower := (rows 11 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 4, region := (rows 5 2 4 12 0), good := (rows 11 3 15 8 0) }] }

theorem profile0_node38 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 5 profile0_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 5 profile0_node38_cert).mp (by decide +kernel))

def profile0_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node35 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] 5 (by decide) (choices 2) [3,17,18] profile0_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] (choices 2) [3,17,18] profile0_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node36
  · exact profile0_node37
  · exact profile0_node38

def profile0_node40_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 11 22 7 29 21), lower := (rows 11 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 9 28 29 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 7 8 0) }] }

theorem profile0_node40 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] 5 profile0_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] 5 profile0_node40_cert).mp (by decide +kernel))

def profile0_node41_cert : CutBound 5 := { lost := (rows 16 1 0 16 0), upper := (rows 11 22 21 15 23), lower := (rows 11 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 10 22 22 8 16) },{ target := 4, region := (rows 3 2 4 10 0), good := (rows 11 15 5 8 0) }] }

theorem profile0_node41 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 5 profile0_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 5 profile0_node41_cert).mp (by decide +kernel))

def profile0_node42_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 11 22 22 13 21), lower := (rows 11 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) }] }

theorem profile0_node42 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 5 profile0_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 5 profile0_node42_cert).mp (by decide +kernel))

def profile0_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node39 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] 5 (by decide) (choices 2) [3,17,18] profile0_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] (choices 2) [3,17,18] profile0_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node40
  · exact profile0_node41
  · exact profile0_node42

def profile0_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node29 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] 5 (by decide) (choices 2) [5,17,20] profile0_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] (choices 2) [5,17,20] profile0_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node30
  · exact profile0_node35
  · exact profile0_node39

def profile0_node45_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 19 7 7 28 28), lower := (rows 19 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile0_node45 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 5 profile0_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 5 profile0_node45_cert).mp (by decide +kernel))

def profile0_node46_cert : CutBound 5 := { lost := (rows 0 16 0 1 0), upper := (rows 19 7 13 30 22), lower := (rows 19 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 12 8 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 3 7 15 8 0) }] }

theorem profile0_node46 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] 5 profile0_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] 5 profile0_node46_cert).mp (by decide +kernel))

def profile0_node48_cert : Bound 5 := { allowed := (rows 4 16 17 4 0), upper := (rows 19 7 14 25 20), lower := (rows 19 7 14 25 16), losses := [{ target := 1, region := (rows 1 0 4 11 22), good := (rows 25 29 28 25 16) }] }

theorem profile0_node48 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 5 profile0_node48_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 5 profile0_node48_cert).mp (by decide +kernel))

def profile0_node49_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 19 7 14 28 17), lower := (rows 19 7 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 9 16), good := (rows 30 14 14 28 16) }] }

theorem profile0_node49 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 5 profile0_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 5 profile0_node49_cert).mp (by decide +kernel))

def profile0_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node47 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] 5 (by decide) (choices 2) [17,20] profile0_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] (choices 2) [17,20] profile0_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node48
  · exact profile0_node49

def profile0_node50_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 19 7 21 14 30), lower := (rows 19 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 5 21 8 16) }] }

theorem profile0_node50 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 5 profile0_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 5 profile0_node50_cert).mp (by decide +kernel))

def profile0_node51_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 19 7 22 13 29), lower := (rows 19 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 6 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) }] }

theorem profile0_node51 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 5 profile0_node51_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 5 profile0_node51_cert).mp (by decide +kernel))

def profile0_node53_cert : Bound 5 := { allowed := (rows 4 16 2 20 0), upper := (rows 19 7 28 11 20), lower := (rows 19 7 28 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 30), good := (rows 18 22 28 30 16) }] }

theorem profile0_node53 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 5 profile0_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 5 profile0_node53_cert).mp (by decide +kernel))

def profile0_node54_cert : Bound 5 := { allowed := (rows 4 16 2 18 0), upper := (rows 19 7 28 13 18), lower := (rows 19 7 28 13 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 18 22 28 28 16) }] }

theorem profile0_node54 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 5 profile0_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 5 profile0_node54_cert).mp (by decide +kernel))

def profile0_node55_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 19 7 28 14 17), lower := (rows 19 7 28 14 16), losses := [{ target := 0, region := (rows 0 2 5 11 16), good := (rows 30 14 28 14 16) }] }

theorem profile0_node55 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 5 profile0_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 5 profile0_node55_cert).mp (by decide +kernel))

def profile0_node52_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node52 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] 5 (by decide) (choices 2) [3,5,6] profile0_node52_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] (choices 2) [3,5,6] profile0_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node53
  · exact profile0_node54
  · exact profile0_node55

def profile0_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node44 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] 5 (by decide) (choices 2) [3,9,10,17,18,24] profile0_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] (choices 2) [3,9,10,17,18,24] profile0_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node45
  · exact profile0_node46
  · exact profile0_node47
  · exact profile0_node50
  · exact profile0_node51
  · exact profile0_node52

def profile0_node57_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 19 11 7 28 20), lower := (rows 19 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 18 10 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 17 9 29 8 16) }] }

theorem profile0_node57 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 5 profile0_node57_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 5 profile0_node57_cert).mp (by decide +kernel))

def profile0_node58_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 19 11 21 14 22), lower := (rows 19 11 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 4, region := (rows 1 6 4 12 0), good := (rows 3 11 15 8 0) }] }

theorem profile0_node58 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 5 profile0_node58_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 5 profile0_node58_cert).mp (by decide +kernel))

def profile0_node59_cert : CutBound 5 := { lost := (rows 4 0 1 0 0), upper := (rows 19 11 22 13 21), lower := (rows 19 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 19 11 19 8 16) }] }

theorem profile0_node59 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] 5 profile0_node59_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] 5 profile0_node59_cert).mp (by decide +kernel))

def profile0_node56_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node56 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] 5 (by decide) (choices 2) [3,17,18] profile0_node56_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] (choices 2) [3,17,18] profile0_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node57
  · exact profile0_node58
  · exact profile0_node59

def profile0_node61_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 19 14 7 29 21), lower := (rows 19 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 17 28 29 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 7 14 7 8 0) }] }

theorem profile0_node61 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] 5 profile0_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] 5 profile0_node61_cert).mp (by decide +kernel))

def profile0_node62_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 19 14 21 15 23), lower := (rows 19 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 4, region := (rows 1 6 4 12 0), good := (rows 3 14 15 8 0) }] }

theorem profile0_node62 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 5 profile0_node62_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 5 profile0_node62_cert).mp (by decide +kernel))

def profile0_node63_cert : CutBound 5 := { lost := (rows 4 0 1 0 0), upper := (rows 19 14 22 13 21), lower := (rows 19 14 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 19 11 19 8 16) }] }

theorem profile0_node63 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] 5 profile0_node63_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] 5 profile0_node63_cert).mp (by decide +kernel))

def profile0_node60_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node60 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] 5 (by decide) (choices 2) [3,17,18] profile0_node60_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] (choices 2) [3,17,18] profile0_node60_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node61
  · exact profile0_node62
  · exact profile0_node63

def profile0_node64_cert : CutBound 5 := { lost := (rows 4 4 0 0 0), upper := (rows 19 19 15 15 31), lower := (rows 19 19 4 8 16), losses := [{ target := 2, region := (rows 19 19 0 8 16), good := (rows 19 19 0 8 19) }] }

theorem profile0_node64 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 5 profile0_node64_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 5 profile0_node64_cert).mp (by decide +kernel))

def profile0_node65_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 19 22 15 15 31), lower := (rows 19 22 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 19 19 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile0_node65 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 5 profile0_node65_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 5 profile0_node65_cert).mp (by decide +kernel))

def profile0_node66_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 19 26 7 15 23), lower := (rows 19 26 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 19 27 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile0_node66 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 5 profile0_node66_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 5 profile0_node66_cert).mp (by decide +kernel))

def profile0_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node43 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] 5 (by decide) (choices 2) [5,9,12,17,20,24] profile0_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] (choices 2) [5,9,12,17,20,24] profile0_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node44
  · exact profile0_node56
  · exact profile0_node60
  · exact profile0_node64
  · exact profile0_node65
  · exact profile0_node66

def profile0_node69_cert : CutBound 5 := { lost := (rows 0 16 16 1 0), upper := (rows 25 7 7 30 22), lower := (rows 25 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 24 30 30 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile0_node69 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 5 profile0_node69_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 5 profile0_node69_cert).mp (by decide +kernel))

def profile0_node70_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 25 7 21 14 22), lower := (rows 25 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 24 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 21 8 16) }] }

theorem profile0_node70 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 5 profile0_node70_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 5 profile0_node70_cert).mp (by decide +kernel))

def profile0_node72_cert : Bound 5 := { allowed := (rows 6 16 0 20 0), upper := (rows 25 7 22 11 20), lower := (rows 25 7 22 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 31), good := (rows 28 22 22 30 16) }] }

theorem profile0_node72 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 5 profile0_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 5 profile0_node72_cert).mp (by decide +kernel))

def profile0_node73_cert : Bound 5 := { allowed := (rows 6 16 0 18 0), upper := (rows 25 7 22 13 18), lower := (rows 25 7 22 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 24 22 22 28 16) }] }

theorem profile0_node73 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 5 profile0_node73_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 5 profile0_node73_cert).mp (by decide +kernel))

def profile0_node74_cert : Bound 5 := { allowed := (rows 6 16 1 16 0), upper := (rows 25 7 22 14 17), lower := (rows 25 7 22 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 24 14 30 14 16) }] }

theorem profile0_node74 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 5 profile0_node74_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 5 profile0_node74_cert).mp (by decide +kernel))

def profile0_node71_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node71 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] 5 (by decide) (choices 2) [3,5,6] profile0_node71_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] (choices 2) [3,5,6] profile0_node71_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node72
  · exact profile0_node73
  · exact profile0_node74

def profile0_node68_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node68 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] 5 (by decide) (choices 2) [3,17,18] profile0_node68_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] (choices 2) [3,17,18] profile0_node68_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node69
  · exact profile0_node70
  · exact profile0_node71

def profile0_node75_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 25 19 7 15 23), lower := (rows 25 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 9 15 4 8 0) }] }

theorem profile0_node75 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 5 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 5 profile0_node75_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 5 profile0_node75_cert).mp (by decide +kernel))

def profile0_node78_cert : Bound 5 := { allowed := (rows 6 0 16 20 0), upper := (rows 25 22 7 11 20), lower := (rows 25 22 7 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 24 22 22 26 16) }] }

theorem profile0_node78 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 5 profile0_node78_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 5 profile0_node78_cert).mp (by decide +kernel))

def profile0_node79_cert : Bound 5 := { allowed := (rows 6 0 16 18 0), upper := (rows 25 22 7 13 18), lower := (rows 25 22 7 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 31), good := (rows 26 22 22 30 16) }] }

theorem profile0_node79 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 5 profile0_node79_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 5 profile0_node79_cert).mp (by decide +kernel))

def profile0_node80_cert : Bound 5 := { allowed := (rows 6 1 16 16 0), upper := (rows 25 22 7 14 17), lower := (rows 25 22 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 24 30 14 14 16) }] }

theorem profile0_node80 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 5 :=
  bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 5 profile0_node80_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 5 profile0_node80_cert).mp (by decide +kernel))

def profile0_node77_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node77 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] 5 (by decide) (choices 2) [3,5,6] profile0_node77_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] (choices 2) [3,5,6] profile0_node77_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node78
  · exact profile0_node79
  · exact profile0_node80

def profile0_node76_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node76 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] 5 (by decide) (choices 2) [3] profile0_node76_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] (choices 2) [3] profile0_node76_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node77

def profile0_node67_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node67 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] 5 (by decide) (choices 2) [5,17,20] profile0_node67_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] (choices 2) [5,17,20] profile0_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node68
  · exact profile0_node75
  · exact profile0_node76

def profile0_node0_route : Route 5 := (fun mask => match mask with | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 5 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 5 (by decide) (choices 2) [6,10,18,24] profile0_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] (choices 2) [6,10,18,24] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node1
  · exact profile0_node29
  · exact profile0_node43
  · exact profile0_node67

theorem profile0 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 5 := profile0_node0

def catalogue : List (List Nat) := [[18,33,34,34,34]]

theorem catalogue_eq : hardProfiles 5 9 5 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 5 9 5 false) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 5 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0
theorem profile_upper (xs : List Nat) (member : xs∈profiles 5 false 5 0 9 9) :
    Upper (n:=5) (D xs.reverse) (R xs.reverse) [] 5 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 5)) (loops : Loopless E) (budget : arcCount E=9)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (false=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤5 := by
  have od (x) : SparseSupport.outdegree E x<5 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<5 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 5).map (SparseSupport.outdegree E)).sum=9 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 5).map (SparseSupport.indegree E)).sum=9 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetNineFinite5
