import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
6 vertices with 8 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetEightFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f : Nat) : Rows 6 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32]
  | 2 => [3,5,9,17,33,6,10,18,34,12,20,36,24,40,48]
  | 3 => [7,11,19,35,13,21,37,25,41,49,14,22,38,26,42,50,28,44,52,56]
  | 4 => [15,23,39,27,43,51,29,45,53,57,30,46,54,58,60]
  | 5 => [31,47,55,59,61,62]
  | 6 => [63]
  | _ => []

theorem cover (d : Fin 7) : RowCover 6 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node2_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 19 39 43 51 35), lower := (rows 19 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 35), good := (rows 47 47 4 8 0 32) }] }

theorem profile0_node2 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,17] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,17] 4 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,17] 4 profile0_node2_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 19 35 7 56 48 48), lower := (rows 19 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 58 62 56 56 56) },{ target := 1, region := (rows 1 0 4 63 63 63), good := (rows 57 57 61 56 56 56) }] }

theorem profile0_node4 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,3] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,3] 4 profile0_node4_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,3] 4 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 19 35 21 42 50 34), lower := (rows 19 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 58 60 8 16 32) },{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) }] }

theorem profile0_node5 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,17] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,17] 4 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,17] 4 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 35 22 41 49 33), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) },{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 57 60 8 16 32) }] }

theorem profile0_node6 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,18] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,18] 4 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,18] 4 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 19 35 37 26 18 50), lower := (rows 19 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 58 60 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) }] }

theorem profile0_node7 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,33] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,33] 4 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,33] 4 profile0_node7_cert).mp (by decide +kernel))

def profile0_node8_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 35 38 25 17 49), lower := (rows 19 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 22 38 38 8 16 32) },{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 57 60 8 16 32) }] }

theorem profile0_node8 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,34] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,34] 4 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,34] 4 profile0_node8_cert).mp (by decide +kernel))

def profile0_node9_cert : CutBound 6 := { lost := (rows 0 16 0 16 0 0), upper := (rows 19 35 52 11 19 35), lower := (rows 19 35 52 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 43 43 36 8 0 32) }] }

theorem profile0_node9 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,48] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,48] 4 profile0_node9_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33,48] 4 profile0_node9_cert).mp (by decide +kernel))

def profile0_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33] 4 := by
  apply routed_branch (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33] 4 (by decide) (choices 2) [3,17,18,33,34,48] profile0_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,33] (choices 2) [3,17,18,33,34,48] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7
  · exact profile0_node8
  · exact profile0_node9

def profile0_node10_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 50 39 43 51 35), lower := (rows 19 50 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 34 4 8 0 32) }] }

theorem profile0_node10 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,48] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,48] 4 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18,48] 4 profile0_node10_cert).mp (by decide +kernel))

def profile0_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18] 4 := by
  apply routed_branch (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18] 4 (by decide) (choices 2) [17,33,48] profile0_node1_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [18] (choices 2) [17,33,48] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node10

def profile0_node12_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 49 19 39 43 51 35), lower := (rows 49 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 33 47 4 8 0 32) }] }

theorem profile0_node12 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,17] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,17] 4 profile0_node12_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,17] 4 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : CutBound 6 := { lost := (rows 2 1 0 0 0 0), upper := (rows 49 50 7 11 19 35), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) },{ target := 1, region := (rows 3 0 4 8 16 32), good := (rows 49 49 4 8 16 32) }] }

theorem profile0_node13 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,48] 4 :=
  cut_bound_sound (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,48] 4 profile0_node13_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48,48] 4 profile0_node13_cert).mp (by decide +kernel))

def profile0_node11_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node11 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48] 4 := by
  apply routed_branch (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48] 4 (by decide) (choices 2) [17,48] profile0_node11_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [48] (choices 2) [17,48] profile0_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node12
  · exact profile0_node13

def profile0_node0_route : Route 6 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [] 4 := by
  apply routed_branch (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [] 4 (by decide) (choices 2) [18,48] profile0_node0_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [] (choices 2) [18,48] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node11

theorem profile0 : Upper (D (n:=6) [34,34,32,32,2,2]) (R (n:=6) [34,34,32,32,2,2]) [] 4 := profile0_node0

def profile1_node3_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 21 40 48 32), lower := (rows 7 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 60 56 56 56) }] }

theorem profile1_node3 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,17] 4 profile1_node3_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,17] 4 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 37 56 48 48), lower := (rows 7 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 60 56 56 56) }] }

theorem profile1_node4 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,33] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,33] 4 profile1_node4_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,33] 4 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 19 52 41 49 33), lower := (rows 7 19 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 47 43 36 8 0 32) }] }

theorem profile1_node5 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,48] 4 profile1_node5_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17,48] 4 profile1_node5_cert).mp (by decide +kernel))

def profile1_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node2 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17] 4 (by decide) (choices 2) [17,33,48] profile1_node2_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,17] (choices 2) [17,33,48] profile1_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node5

def profile1_node7_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 50 21 41 49 33), lower := (rows 7 50 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 13 0 37), good := (rows 47 34 45 8 0 32) }] }

theorem profile1_node7 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,17] 4 profile1_node7_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,17] 4 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 7 50 52 9 17 33), lower := (rows 7 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 6 54 54 8 16 32) }] }

theorem profile1_node8 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,48] 4 profile1_node8_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48,48] 4 profile1_node8_cert).mp (by decide +kernel))

def profile1_node6_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node6 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48] 4 (by decide) (choices 2) [17,48] profile1_node6_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6,48] (choices 2) [17,48] profile1_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node7
  · exact profile1_node8

def profile1_node1_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6] 4 (by decide) (choices 2) [17,48] profile1_node1_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [6] (choices 2) [17,48] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node2
  · exact profile1_node6

def profile1_node11_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 21 40 48 32), lower := (rows 19 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 62 60 56 56 56) }] }

theorem profile1_node11 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,17] 4 profile1_node11_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,17] 4 profile1_node11_cert).mp (by decide +kernel))

def profile1_node12_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 37 56 48 48), lower := (rows 19 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 62 60 56 56 56) }] }

theorem profile1_node12 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,33] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,33] 4 profile1_node12_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,33] 4 profile1_node12_cert).mp (by decide +kernel))

def profile1_node13_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 19 7 52 41 49 33), lower := (rows 19 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 43 47 36 8 0 32) }] }

theorem profile1_node13 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,48] 4 profile1_node13_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5,48] 4 profile1_node13_cert).mp (by decide +kernel))

def profile1_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node10 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5] 4 (by decide) (choices 2) [17,33,48] profile1_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,5] (choices 2) [17,33,48] profile1_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node11
  · exact profile1_node12
  · exact profile1_node13

def profile1_node14_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 19 37 45 53 37), lower := (rows 19 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 35), good := (rows 47 47 4 8 0 32) }] }

theorem profile1_node14 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,17] 4 profile1_node14_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,17] 4 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 22 37 41 49 33), lower := (rows 19 22 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 6 4 8 0 32) }] }

theorem profile1_node15 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,20] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,20] 4 profile1_node15_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,20] 4 profile1_node15_cert).mp (by decide +kernel))

def profile1_node17_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 21 44 52 36), lower := (rows 19 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 60 8 16 32) }] }

theorem profile1_node17 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,17] 4 profile1_node17_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,17] 4 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 37 28 20 52), lower := (rows 19 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 60 8 16 32) }] }

theorem profile1_node18 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,33] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,33] 4 profile1_node18_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,33] 4 profile1_node18_cert).mp (by decide +kernel))

def profile1_node20_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 52 13 16 32), lower := (rows 19 35 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 54 52 60 52 52) }] }

theorem profile1_node20 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48,5] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48,5] 4 profile1_node20_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48,5] 4 profile1_node20_cert).mp (by decide +kernel))

def profile1_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node19 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48] 4 (by decide) (choices 2) [5] profile1_node19_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33,48] (choices 2) [5] profile1_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node20

def profile1_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node16 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33] 4 (by decide) (choices 2) [17,33,48] profile1_node16_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,33] (choices 2) [17,33,48] profile1_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node17
  · exact profile1_node18
  · exact profile1_node19

def profile1_node22_cert : CutBound 6 := { lost := (rows 0 16 0 16 0 0), upper := (rows 19 38 21 41 49 33), lower := (rows 19 38 21 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 13 0 37), good := (rows 43 46 47 8 0 32) }] }

theorem profile1_node22 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,17] 4 profile1_node22_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,17] 4 profile1_node22_cert).mp (by decide +kernel))

def profile1_node23_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 37 25 17 49), lower := (rows 19 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 38 8 16 32) }] }

theorem profile1_node23 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,33] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,33] 4 profile1_node23_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,33] 4 profile1_node23_cert).mp (by decide +kernel))

def profile1_node24_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 52 9 17 33), lower := (rows 19 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 54 8 16 32) }] }

theorem profile1_node24 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,48] 4 profile1_node24_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36,48] 4 profile1_node24_cert).mp (by decide +kernel))

def profile1_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node21 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36] 4 (by decide) (choices 2) [17,33,48] profile1_node21_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,36] (choices 2) [17,33,48] profile1_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node22
  · exact profile1_node23
  · exact profile1_node24

def profile1_node25_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 50 37 45 53 37), lower := (rows 19 50 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 34 4 8 0 32) }] }

theorem profile1_node25 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,48] 4 profile1_node25_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18,48] 4 profile1_node25_cert).mp (by decide +kernel))

def profile1_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node9 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18] 4 (by decide) (choices 2) [5,17,20,33,36,48] profile1_node9_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [18] (choices 2) [5,17,20,33,36,48] profile1_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node10
  · exact profile1_node14
  · exact profile1_node15
  · exact profile1_node16
  · exact profile1_node21
  · exact profile1_node25

def profile1_node28_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 7 56 48 48), lower := (rows 49 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 56 62 62 56 56 56) }] }

theorem profile1_node28 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,3] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,3] 4 profile1_node28_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,3] 4 profile1_node28_cert).mp (by decide +kernel))

def profile1_node29_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 21 42 50 34), lower := (rows 49 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 20 8 16 32) }] }

theorem profile1_node29 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,17] 4 profile1_node29_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,17] 4 profile1_node29_cert).mp (by decide +kernel))

def profile1_node30_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 7 22 41 49 33), lower := (rows 49 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 41 47 46 8 0 32) }] }

theorem profile1_node30 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,18] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,18] 4 profile1_node30_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,18] 4 profile1_node30_cert).mp (by decide +kernel))

def profile1_node31_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 7 52 11 19 35), lower := (rows 49 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 6 52 8 16 32) }] }

theorem profile1_node31 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,48] 4 profile1_node31_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5,48] 4 profile1_node31_cert).mp (by decide +kernel))

def profile1_node27_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node27 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5] 4 (by decide) (choices 2) [3,17,18,48] profile1_node27_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,5] (choices 2) [3,17,18,48] profile1_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node28
  · exact profile1_node29
  · exact profile1_node30
  · exact profile1_node31

def profile1_node32_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 49 19 39 47 55 39), lower := (rows 49 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 33 47 4 8 0 32) }] }

theorem profile1_node32 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,17] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,17] 4 profile1_node32_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,17] 4 profile1_node32_cert).mp (by decide +kernel))

def profile1_node34_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 22 7 41 49 33), lower := (rows 49 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 13 0 37), good := (rows 41 46 47 8 0 32) }] }

theorem profile1_node34 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,3] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,3] 4 profile1_node34_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,3] 4 profile1_node34_cert).mp (by decide +kernel))

def profile1_node35_cert : CutBound 6 := { lost := (rows 0 0 16 0 0 0), upper := (rows 49 22 37 11 19 35), lower := (rows 49 22 37 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 37 6 37 8 0 32) }] }

theorem profile1_node35 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,33] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,33] 4 profile1_node35_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,33] 4 profile1_node35_cert).mp (by decide +kernel))

def profile1_node36_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 38 9 17 33), lower := (rows 49 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 8 16 32) }] }

theorem profile1_node36 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,34] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,34] 4 profile1_node36_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20,34] 4 profile1_node36_cert).mp (by decide +kernel))

def profile1_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile1_node33 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20] 4 (by decide) (choices 2) [3,33,34] profile1_node33_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,20] (choices 2) [3,33,34] profile1_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node34
  · exact profile1_node35
  · exact profile1_node36

def profile1_node37_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 50 7 15 23 39), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) }] }

theorem profile1_node37 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,48] 4 :=
  cut_bound_sound (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,48] 4 profile1_node37_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48,48] 4 profile1_node37_cert).mp (by decide +kernel))

def profile1_node26_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node26 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48] 4 (by decide) (choices 2) [5,17,20,48] profile1_node26_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [48] (choices 2) [5,17,20,48] profile1_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node27
  · exact profile1_node32
  · exact profile1_node33
  · exact profile1_node37

def profile1_node0_route : Route 6 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [] 4 := by
  apply routed_branch (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [] 4 (by decide) (choices 2) [6,18,48] profile1_node0_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [] (choices 2) [6,18,48] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node9
  · exact profile1_node26

theorem profile1 : Upper (D (n:=6) [34,33,33,32,2,2]) (R (n:=6) [34,33,33,32,2,2]) [] 4 := profile1_node0

def profile2_node2_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 25 11 53 57 49 49), lower := (rows 25 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 7 0 19 35), good := (rows 53 55 4 0 16 32) }] }

theorem profile2_node2 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,9] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,9] 4 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,9] 4 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 26 37 41 49 33), lower := (rows 25 26 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 26 26 4 8 16 32) }] }

theorem profile2_node3 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,24] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,24] 4 profile2_node3_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,24] 4 profile2_node3_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 25 35 13 56 48 48), lower := (rows 25 35 13 8 16 32), losses := [{ target := 3, region := (rows 1 7 4 0 63 63), good := (rows 51 51 55 48 48 48) }] }

theorem profile2_node5 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,9] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,9] 4 profile2_node5_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,9] 4 profile2_node5_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 35 28 41 49 33), lower := (rows 25 35 28 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 28 38 28 8 16 32) }] }

theorem profile2_node6 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,24] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,24] 4 profile2_node6_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,24] 4 profile2_node6_cert).mp (by decide +kernel))

def profile2_node7_cert : CutBound 6 := { lost := (rows 0 8 8 0 0 0), upper := (rows 25 35 37 24 24 56), lower := (rows 25 35 37 8 16 32), losses := [{ target := 3, region := (rows 1 6 6 0 16 32), good := (rows 17 39 39 0 16 32) }] }

theorem profile2_node7 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,33] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,33] 4 profile2_node7_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,33] 4 profile2_node7_cert).mp (by decide +kernel))

def profile2_node8_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 25 35 44 25 17 49), lower := (rows 25 35 44 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 19 35), good := (rows 51 51 36 0 16 32) }] }

theorem profile2_node8 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,40] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,40] 4 profile2_node8_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33,40] 4 profile2_node8_cert).mp (by decide +kernel))

def profile2_node4_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node4 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33] 4 := by
  apply routed_branch (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33] 4 (by decide) (choices 2) [9,24,33,40] profile2_node4_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,33] (choices 2) [9,24,33,40] profile2_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node5
  · exact profile2_node6
  · exact profile2_node7
  · exact profile2_node8

def profile2_node9_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 25 42 53 57 49 49), lower := (rows 25 42 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 53 34 4 0 16 32) }] }

theorem profile2_node9 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,40] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,40] 4 profile2_node9_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24,40] 4 profile2_node9_cert).mp (by decide +kernel))

def profile2_node1_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24] 4 := by
  apply routed_branch (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24] 4 (by decide) (choices 2) [9,24,33,40] profile2_node1_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [24] (choices 2) [9,24,33,40] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node9

def profile2_node11_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 41 11 53 57 49 49), lower := (rows 41 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 7 0 19 35), good := (rows 53 55 4 0 16 32) }] }

theorem profile2_node11 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,9] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,9] 4 profile2_node11_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,9] 4 profile2_node11_cert).mp (by decide +kernel))

def profile2_node13_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 41 19 13 56 48 48), lower := (rows 41 19 13 8 16 32), losses := [{ target := 3, region := (rows 1 7 4 0 63 63), good := (rows 51 51 55 48 48 48) }] }

theorem profile2_node13 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,9] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,9] 4 profile2_node13_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,9] 4 profile2_node13_cert).mp (by decide +kernel))

def profile2_node14_cert : CutBound 6 := { lost := (rows 0 8 8 0 0 0), upper := (rows 41 19 21 40 56 40), lower := (rows 41 19 21 8 16 32), losses := [{ target := 3, region := (rows 1 6 6 0 16 32), good := (rows 33 23 23 0 16 32) }] }

theorem profile2_node14 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,17] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,17] 4 profile2_node14_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,17] 4 profile2_node14_cert).mp (by decide +kernel))

def profile2_node15_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 41 19 28 41 49 33), lower := (rows 41 19 28 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 19 35), good := (rows 51 51 20 0 16 32) }] }

theorem profile2_node15 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,24] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,24] 4 profile2_node15_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,24] 4 profile2_node15_cert).mp (by decide +kernel))

def profile2_node16_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 41 19 37 24 24 56), lower := (rows 41 19 37 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 16 32), good := (rows 37 23 37 0 16 32) }] }

theorem profile2_node16 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,33] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,33] 4 profile2_node16_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,33] 4 profile2_node16_cert).mp (by decide +kernel))

def profile2_node17_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 41 19 44 25 17 49), lower := (rows 41 19 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 44 22 44 8 16 32) }] }

theorem profile2_node17 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,40] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,40] 4 profile2_node17_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,40] 4 profile2_node17_cert).mp (by decide +kernel))

def profile2_node18_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 41 19 52 9 25 41), lower := (rows 41 19 52 8 16 32), losses := [{ target := 4, region := (rows 63 2 4 63 0 63), good := (rows 41 43 45 41 41 41) }] }

theorem profile2_node18 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,48] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,48] 4 profile2_node18_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17,48] 4 profile2_node18_cert).mp (by decide +kernel))

def profile2_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node12 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17] 4 := by
  apply routed_branch (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17] 4 (by decide) (choices 2) [9,17,24,33,40,48] profile2_node12_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,17] (choices 2) [9,17,24,33,40,48] profile2_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node13
  · exact profile2_node14
  · exact profile2_node15
  · exact profile2_node16
  · exact profile2_node17
  · exact profile2_node18

def profile2_node19_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 41 26 53 57 49 49), lower := (rows 41 26 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 53 18 4 0 16 32) }] }

theorem profile2_node19 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,24] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,24] 4 profile2_node19_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,24] 4 profile2_node19_cert).mp (by decide +kernel))

def profile2_node20_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 41 35 29 25 25 57), lower := (rows 41 35 4 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 16 32), good := (rows 35 35 4 0 16 32) }] }

theorem profile2_node20 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,33] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,33] 4 profile2_node20_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,33] 4 profile2_node20_cert).mp (by decide +kernel))

def profile2_node21_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 41 42 21 25 17 49), lower := (rows 41 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 42 42 4 8 16 32) }] }

theorem profile2_node21 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,40] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,40] 4 profile2_node21_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,40] 4 profile2_node21_cert).mp (by decide +kernel))

def profile2_node22_cert : CutBound 6 := { lost := (rows 0 0 32 0 0 0), upper := (rows 41 50 29 25 25 57), lower := (rows 41 50 4 8 16 32), losses := [{ target := 5, region := (rows 1 2 5 9 17 0), good := (rows 29 18 4 8 16 0) }] }

theorem profile2_node22 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,48] 4 :=
  cut_bound_sound (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,48] 4 profile2_node22_cert
    ((SmallCut.boundCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40,48] 4 profile2_node22_cert).mp (by decide +kernel))

def profile2_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node10 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40] 4 := by
  apply routed_branch (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40] 4 (by decide) (choices 2) [9,17,24,33,40,48] profile2_node10_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [40] (choices 2) [9,17,24,33,40,48] profile2_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node11
  · exact profile2_node12
  · exact profile2_node19
  · exact profile2_node20
  · exact profile2_node21
  · exact profile2_node22

def profile2_node0_route : Route 6 := (fun mask => match mask with | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [] 4 := by
  apply routed_branch (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [] 4 (by decide) (choices 2) [24,40] profile2_node0_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [] (choices 2) [24,40] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node1
  · exact profile2_node10

theorem profile2 : Upper (D (n:=6) [34,32,32,18,18,2]) (R (n:=6) [34,32,32,18,18,2]) [] 4 := profile2_node0

def profile3_node2_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 11 11 52 56 48 48), lower := (rows 11 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 63 0 63 63), good := (rows 55 55 52 52 52 52) }] }

theorem profile3_node2 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,9] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,9] 4 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,9] 4 profile3_node2_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 11 19 28 40 48 32), lower := (rows 11 19 28 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node4 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,24] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,24] 4 profile3_node4_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,24] 4 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 11 19 44 56 48 48), lower := (rows 11 19 44 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node5 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,40] 4 profile3_node5_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,40] 4 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 11 19 52 40 56 40), lower := (rows 11 19 52 8 16 32), losses := [{ target := 4, region := (rows 3 2 4 63 0 63), good := (rows 43 43 44 40 40 40) }] }

theorem profile3_node6 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,48] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,48] 4 profile3_node6_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17,48] 4 profile3_node6_cert).mp (by decide +kernel))

def profile3_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17] 4 (by decide) (choices 2) [24,40,48] profile3_node3_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,17] (choices 2) [24,40,48] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6

def profile3_node7_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 11 26 53 57 49 49), lower := (rows 11 26 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 55 18 4 0 16 32) }] }

theorem profile3_node7 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,24] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,24] 4 profile3_node7_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,24] 4 profile3_node7_cert).mp (by decide +kernel))

def profile3_node9_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 11 35 28 56 48 48), lower := (rows 11 35 28 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node9 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,24] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,24] 4 profile3_node9_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,24] 4 profile3_node9_cert).mp (by decide +kernel))

def profile3_node10_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 11 35 44 24 16 48), lower := (rows 11 35 44 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node10 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,40] 4 profile3_node10_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,40] 4 profile3_node10_cert).mp (by decide +kernel))

def profile3_node11_cert : CutBound 6 := { lost := (rows 32 0 0 0 0 0), upper := (rows 11 35 52 24 24 56), lower := (rows 11 35 52 8 16 32), losses := [{ target := 5, region := (rows 3 2 4 63 63 0), good := (rows 27 27 28 24 24 24) }] }

theorem profile3_node11 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,48] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,48] 4 profile3_node11_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33,48] 4 profile3_node11_cert).mp (by decide +kernel))

def profile3_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node8 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33] 4 (by decide) (choices 2) [24,40,48] profile3_node8_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,33] (choices 2) [24,40,48] profile3_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node9
  · exact profile3_node10
  · exact profile3_node11

def profile3_node12_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 11 42 53 57 49 49), lower := (rows 11 42 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 17 33), good := (rows 55 34 4 0 16 32) }] }

theorem profile3_node12 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,40] 4 profile3_node12_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,40] 4 profile3_node12_cert).mp (by decide +kernel))

def profile3_node14_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 11 50 13 56 48 48), lower := (rows 11 50 13 8 16 32), losses := [{ target := 3, region := (rows 1 63 4 0 63 63), good := (rows 51 50 55 50 50 50) }] }

theorem profile3_node14 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,9] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,9] 4 profile3_node14_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,9] 4 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 11 50 21 40 56 40), lower := (rows 11 50 21 8 16 32), losses := [{ target := 4, region := (rows 3 2 4 63 0 63), good := (rows 43 43 45 40 40 40) }] }

theorem profile3_node15 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,17] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,17] 4 profile3_node15_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,17] 4 profile3_node15_cert).mp (by decide +kernel))

def profile3_node16_cert : Bound 6 := { allowed := (rows 48 8 32 0 0 0), upper := (rows 11 50 28 41 49 33), lower := (rows 11 50 28 8 16 32), losses := [] }

theorem profile3_node16 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,24] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,24] 4 profile3_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,24] 4 profile3_node16_cert).mp (by decide +kernel))

def profile3_node17_cert : CutBound 6 := { lost := (rows 32 0 0 0 0 0), upper := (rows 11 50 37 24 24 56), lower := (rows 11 50 37 8 16 32), losses := [{ target := 5, region := (rows 3 2 4 63 63 0), good := (rows 27 27 29 24 24 24) }] }

theorem profile3_node17 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,33] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,33] 4 profile3_node17_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,33] 4 profile3_node17_cert).mp (by decide +kernel))

def profile3_node18_cert : Bound 6 := { allowed := (rows 48 8 16 0 0 0), upper := (rows 11 50 44 25 17 49), lower := (rows 11 50 44 8 16 32), losses := [] }

theorem profile3_node18 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,40] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,40] 4 profile3_node18_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,40] 4 profile3_node18_cert).mp (by decide +kernel))

def profile3_node19_cert : Bound 6 := { allowed := (rows 48 8 8 0 0 0), upper := (rows 11 50 52 9 25 41), lower := (rows 11 50 52 8 16 32), losses := [] }

theorem profile3_node19 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,48] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,48] 4 profile3_node19_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48,48] 4 profile3_node19_cert).mp (by decide +kernel))

def profile3_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node13 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48] 4 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node13_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10,48] (choices 2) [9,17,24,33,40,48] profile3_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node14
  · exact profile3_node15
  · exact profile3_node16
  · exact profile3_node17
  · exact profile3_node18
  · exact profile3_node19

def profile3_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10] 4 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node1_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [10] (choices 2) [9,17,24,33,40,48] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node3
  · exact profile3_node7
  · exact profile3_node8
  · exact profile3_node12
  · exact profile3_node13

def profile3_node21_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 25 11 54 58 50 50), lower := (rows 25 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 6 0 18 34), good := (rows 17 55 4 0 16 32) }] }

theorem profile3_node21 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,9] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,9] 4 profile3_node21_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,9] 4 profile3_node21_cert).mp (by decide +kernel))

def profile3_node22_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 25 26 39 43 51 35), lower := (rows 25 26 4 8 16 32), losses := [{ target := 5, region := (rows 3 3 4 8 16 0), good := (rows 27 27 4 8 16 0) }] }

theorem profile3_node22 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,24] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,24] 4 profile3_node22_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,24] 4 profile3_node22_cert).mp (by decide +kernel))

def profile3_node24_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 25 35 14 56 48 48), lower := (rows 25 35 14 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 54 48 48 48) }] }

theorem profile3_node24 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,10] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,10] 4 profile3_node24_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,10] 4 profile3_node24_cert).mp (by decide +kernel))

def profile3_node25_cert : Bound 6 := { allowed := (rows 32 24 32 0 0 0), upper := (rows 25 35 28 42 50 34), lower := (rows 25 35 28 8 16 32), losses := [] }

theorem profile3_node25 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,24] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,24] 4 profile3_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,24] 4 profile3_node25_cert).mp (by decide +kernel))

def profile3_node26_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 25 35 38 24 24 56), lower := (rows 25 35 38 8 16 32), losses := [{ target := 3, region := (rows 1 2 6 0 16 32), good := (rows 17 39 38 0 16 32) }] }

theorem profile3_node26 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,34] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,34] 4 profile3_node26_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,34] 4 profile3_node26_cert).mp (by decide +kernel))

def profile3_node27_cert : Bound 6 := { allowed := (rows 32 24 16 0 0 0), upper := (rows 25 35 44 26 18 50), lower := (rows 25 35 44 8 16 32), losses := [] }

theorem profile3_node27 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,40] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,40] 4 profile3_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33,40] 4 profile3_node27_cert).mp (by decide +kernel))

def profile3_node23_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node23 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33] 4 (by decide) (choices 2) [10,24,34,40] profile3_node23_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,33] (choices 2) [10,24,34,40] profile3_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node24
  · exact profile3_node25
  · exact profile3_node26
  · exact profile3_node27

def profile3_node30_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 42 7 24 48 32), lower := (rows 25 42 7 24 16 32), losses := [{ target := 4, region := (rows 1 11 5 8 0 63), good := (rows 47 42 39 42 32 32) }] }

theorem profile3_node30 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,16] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,16] 4 profile3_node30_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,16] 4 profile3_node30_cert).mp (by decide +kernel))

def profile3_node31_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 25 42 7 40 16 48), lower := (rows 25 42 7 40 16 32), losses := [{ target := 4, region := (rows 1 42 5 42 0 32), good := (rows 15 42 15 42 0 42) }] }

theorem profile3_node31 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,32] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,32] 4 profile3_node31_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3,32] 4 profile3_node31_cert).mp (by decide +kernel))

def profile3_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node29 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3] 4 (by decide) (choices 1) [16,32] profile3_node29_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,3] (choices 1) [16,32] profile3_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node30
  · exact profile3_node31

def profile3_node32_cert : Bound 6 := { allowed := (rows 32 16 40 0 0 0), upper := (rows 25 42 21 42 50 34), lower := (rows 25 42 21 8 16 32), losses := [] }

theorem profile3_node32 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,17] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,17] 4 profile3_node32_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,17] 4 profile3_node32_cert).mp (by decide +kernel))

def profile3_node33_cert : Bound 6 := { allowed := (rows 32 16 40 0 0 0), upper := (rows 25 42 22 41 49 33), lower := (rows 25 42 22 8 16 32), losses := [] }

theorem profile3_node33 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,18] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,18] 4 profile3_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,18] 4 profile3_node33_cert).mp (by decide +kernel))

def profile3_node34_cert : Bound 6 := { allowed := (rows 32 16 24 0 0 0), upper := (rows 25 42 37 26 18 50), lower := (rows 25 42 37 8 16 32), losses := [] }

theorem profile3_node34 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,33] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,33] 4 profile3_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,33] 4 profile3_node34_cert).mp (by decide +kernel))

def profile3_node35_cert : Bound 6 := { allowed := (rows 32 16 24 0 0 0), upper := (rows 25 42 38 25 17 49), lower := (rows 25 42 38 8 16 32), losses := [] }

theorem profile3_node35 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,34] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,34] 4 profile3_node35_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,34] 4 profile3_node35_cert).mp (by decide +kernel))

def profile3_node36_cert : Bound 6 := { allowed := (rows 32 16 8 0 0 0), upper := (rows 25 42 52 11 19 35), lower := (rows 25 42 52 8 16 32), losses := [] }

theorem profile3_node36 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,48] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,48] 4 profile3_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40,48] 4 profile3_node36_cert).mp (by decide +kernel))

def profile3_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node28 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40] 4 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node28_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24,40] (choices 2) [3,17,18,33,34,48] profile3_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node29
  · exact profile3_node32
  · exact profile3_node33
  · exact profile3_node34
  · exact profile3_node35
  · exact profile3_node36

def profile3_node20_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node20 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24] 4 (by decide) (choices 2) [9,24,33,40] profile3_node20_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [24] (choices 2) [9,24,33,40] profile3_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node21
  · exact profile3_node22
  · exact profile3_node23
  · exact profile3_node28

def profile3_node39_cert : CutBound 6 := { lost := (rows 8 0 0 0 0 0), upper := (rows 35 11 28 56 48 48), lower := (rows 35 11 28 8 16 32), losses := [{ target := 3, region := (rows 3 2 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node39 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,24] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,24] 4 profile3_node39_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,24] 4 profile3_node39_cert).mp (by decide +kernel))

def profile3_node40_cert : CutBound 6 := { lost := (rows 8 0 0 0 0 0), upper := (rows 35 11 44 24 16 48), lower := (rows 35 11 44 8 16 32), losses := [{ target := 3, region := (rows 3 2 4 0 63 63), good := (rows 51 51 52 48 48 48) }] }

theorem profile3_node40 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,40] 4 profile3_node40_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,40] 4 profile3_node40_cert).mp (by decide +kernel))

def profile3_node41_cert : CutBound 6 := { lost := (rows 0 32 0 0 0 0), upper := (rows 35 11 52 24 24 56), lower := (rows 35 11 52 8 16 32), losses := [{ target := 5, region := (rows 1 3 4 63 63 0), good := (rows 27 27 28 24 24 24) }] }

theorem profile3_node41 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,48] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,48] 4 profile3_node41_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9,48] 4 profile3_node41_cert).mp (by decide +kernel))

def profile3_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node38 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9] 4 (by decide) (choices 2) [24,40,48] profile3_node38_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,9] (choices 2) [24,40,48] profile3_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node39
  · exact profile3_node40
  · exact profile3_node41

def profile3_node43_cert : CutBound 6 := { lost := (rows 8 0 0 0 0 0), upper := (rows 35 26 13 56 48 48), lower := (rows 35 26 13 8 16 32), losses := [{ target := 3, region := (rows 3 2 4 0 63 63), good := (rows 51 51 53 48 48 48) }] }

theorem profile3_node43 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,9] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,9] 4 profile3_node43_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,9] 4 profile3_node43_cert).mp (by decide +kernel))

def profile3_node44_cert : Bound 6 := { allowed := (rows 24 32 32 0 0 0), upper := (rows 35 26 28 41 49 33), lower := (rows 35 26 28 8 16 32), losses := [] }

theorem profile3_node44 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,24] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,24] 4 profile3_node44_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,24] 4 profile3_node44_cert).mp (by decide +kernel))

def profile3_node45_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 35 26 37 24 24 56), lower := (rows 35 26 37 8 16 32), losses := [{ target := 3, region := (rows 1 2 5 0 16 32), good := (rows 39 18 37 0 16 32) }] }

theorem profile3_node45 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,33] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,33] 4 profile3_node45_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,33] 4 profile3_node45_cert).mp (by decide +kernel))

def profile3_node46_cert : Bound 6 := { allowed := (rows 24 32 16 0 0 0), upper := (rows 35 26 44 25 17 49), lower := (rows 35 26 44 8 16 32), losses := [] }

theorem profile3_node46 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,40] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,40] 4 profile3_node46_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24,40] 4 profile3_node46_cert).mp (by decide +kernel))

def profile3_node42_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node42 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24] 4 (by decide) (choices 2) [9,24,33,40] profile3_node42_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,24] (choices 2) [9,24,33,40] profile3_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node43
  · exact profile3_node44
  · exact profile3_node45
  · exact profile3_node46

def profile3_node47_cert : CutBound 6 := { lost := (rows 8 8 0 0 0 0), upper := (rows 35 35 28 24 24 56), lower := (rows 35 35 4 8 16 32), losses := [{ target := 3, region := (rows 35 35 4 0 16 32), good := (rows 35 35 4 0 16 35) }] }

theorem profile3_node47 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,33] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,33] 4 profile3_node47_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,33] 4 profile3_node47_cert).mp (by decide +kernel))

def profile3_node48_cert : CutBound 6 := { lost := (rows 8 0 0 0 0 0), upper := (rows 35 42 29 25 25 57), lower := (rows 35 42 4 8 16 32), losses := [{ target := 3, region := (rows 3 2 4 0 16 32), good := (rows 35 35 4 0 16 32) }] }

theorem profile3_node48 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,40] 4 profile3_node48_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34,40] 4 profile3_node48_cert).mp (by decide +kernel))

def profile3_node37_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node37 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34] 4 (by decide) (choices 2) [9,24,33,40] profile3_node37_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [34] (choices 2) [9,24,33,40] profile3_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node38
  · exact profile3_node42
  · exact profile3_node47
  · exact profile3_node48

def profile3_node50_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 41 11 54 58 50 50), lower := (rows 41 11 4 8 16 32), losses := [{ target := 3, region := (rows 1 2 6 0 18 34), good := (rows 33 55 4 0 16 32) }] }

theorem profile3_node50 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,9] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,9] 4 profile3_node50_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,9] 4 profile3_node50_cert).mp (by decide +kernel))

def profile3_node52_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 41 19 14 56 48 48), lower := (rows 41 19 14 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 63 63), good := (rows 51 51 54 48 48 48) }] }

theorem profile3_node52 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,10] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,10] 4 profile3_node52_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,10] 4 profile3_node52_cert).mp (by decide +kernel))

def profile3_node53_cert : CutBound 6 := { lost := (rows 0 0 8 0 0 0), upper := (rows 41 19 22 40 56 40), lower := (rows 41 19 22 8 16 32), losses := [{ target := 3, region := (rows 1 2 6 0 16 32), good := (rows 33 23 22 0 16 32) }] }

theorem profile3_node53 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,18] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,18] 4 profile3_node53_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,18] 4 profile3_node53_cert).mp (by decide +kernel))

def profile3_node54_cert : Bound 6 := { allowed := (rows 16 40 32 0 0 0), upper := (rows 41 19 28 42 50 34), lower := (rows 41 19 28 8 16 32), losses := [] }

theorem profile3_node54 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,24] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,24] 4 profile3_node54_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,24] 4 profile3_node54_cert).mp (by decide +kernel))

def profile3_node55_cert : CutBound 6 := { lost := (rows 0 32 0 0 0 0), upper := (rows 41 19 38 24 24 56), lower := (rows 41 19 38 8 16 32), losses := [{ target := 5, region := (rows 1 3 4 63 63 0), good := (rows 27 27 30 24 24 24) }] }

theorem profile3_node55 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,34] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,34] 4 profile3_node55_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,34] 4 profile3_node55_cert).mp (by decide +kernel))

def profile3_node56_cert : Bound 6 := { allowed := (rows 16 40 16 0 0 0), upper := (rows 41 19 44 26 18 50), lower := (rows 41 19 44 8 16 32), losses := [] }

theorem profile3_node56 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,40] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,40] 4 profile3_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,40] 4 profile3_node56_cert).mp (by decide +kernel))

def profile3_node57_cert : Bound 6 := { allowed := (rows 16 40 8 0 0 0), upper := (rows 41 19 52 10 26 42), lower := (rows 41 19 52 8 16 32), losses := [] }

theorem profile3_node57 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,48] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,48] 4 profile3_node57_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17,48] 4 profile3_node57_cert).mp (by decide +kernel))

def profile3_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node51 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17] 4 (by decide) (choices 2) [10,18,24,34,40,48] profile3_node51_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,17] (choices 2) [10,18,24,34,40,48] profile3_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node52
  · exact profile3_node53
  · exact profile3_node54
  · exact profile3_node55
  · exact profile3_node56
  · exact profile3_node57

def profile3_node60_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 41 26 7 24 48 32), lower := (rows 41 26 7 24 16 32), losses := [{ target := 4, region := (rows 11 2 6 8 0 63), good := (rows 41 47 39 41 32 32) }] }

theorem profile3_node60 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,16] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,16] 4 profile3_node60_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,16] 4 profile3_node60_cert).mp (by decide +kernel))

def profile3_node61_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 41 26 7 40 16 48), lower := (rows 41 26 7 40 16 32), losses := [{ target := 4, region := (rows 41 2 6 41 0 32), good := (rows 41 15 15 41 0 41) }] }

theorem profile3_node61 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,32] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,32] 4 profile3_node61_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3,32] 4 profile3_node61_cert).mp (by decide +kernel))

def profile3_node59_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node59 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3] 4 (by decide) (choices 1) [16,32] profile3_node59_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,3] (choices 1) [16,32] profile3_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node60
  · exact profile3_node61

def profile3_node62_cert : Bound 6 := { allowed := (rows 16 32 40 0 0 0), upper := (rows 41 26 21 42 50 34), lower := (rows 41 26 21 8 16 32), losses := [] }

theorem profile3_node62 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,17] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,17] 4 profile3_node62_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,17] 4 profile3_node62_cert).mp (by decide +kernel))

def profile3_node63_cert : Bound 6 := { allowed := (rows 16 32 40 0 0 0), upper := (rows 41 26 22 41 49 33), lower := (rows 41 26 22 8 16 32), losses := [] }

theorem profile3_node63 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,18] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,18] 4 profile3_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,18] 4 profile3_node63_cert).mp (by decide +kernel))

def profile3_node64_cert : Bound 6 := { allowed := (rows 16 32 24 0 0 0), upper := (rows 41 26 37 26 18 50), lower := (rows 41 26 37 8 16 32), losses := [] }

theorem profile3_node64 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,33] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,33] 4 profile3_node64_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,33] 4 profile3_node64_cert).mp (by decide +kernel))

def profile3_node65_cert : Bound 6 := { allowed := (rows 16 32 24 0 0 0), upper := (rows 41 26 38 25 17 49), lower := (rows 41 26 38 8 16 32), losses := [] }

theorem profile3_node65 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,34] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,34] 4 profile3_node65_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,34] 4 profile3_node65_cert).mp (by decide +kernel))

def profile3_node66_cert : Bound 6 := { allowed := (rows 16 32 8 0 0 0), upper := (rows 41 26 52 11 19 35), lower := (rows 41 26 52 8 16 32), losses := [] }

theorem profile3_node66 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,48] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,48] 4 profile3_node66_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24,48] 4 profile3_node66_cert).mp (by decide +kernel))

def profile3_node58_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node58 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24] 4 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node58_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,24] (choices 2) [3,17,18,33,34,48] profile3_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node59
  · exact profile3_node62
  · exact profile3_node63
  · exact profile3_node64
  · exact profile3_node65
  · exact profile3_node66

def profile3_node67_cert : CutBound 6 := { lost := (rows 0 8 0 0 0 0), upper := (rows 41 35 30 26 26 58), lower := (rows 41 35 4 8 16 32), losses := [{ target := 3, region := (rows 1 3 4 0 16 32), good := (rows 35 35 4 0 16 32) }] }

theorem profile3_node67 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,33] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,33] 4 profile3_node67_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,33] 4 profile3_node67_cert).mp (by decide +kernel))

def profile3_node68_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 41 42 23 27 19 51), lower := (rows 41 42 4 8 16 32), losses := [{ target := 4, region := (rows 3 3 4 8 0 32), good := (rows 43 43 4 8 0 32) }] }

theorem profile3_node68 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,40] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,40] 4 profile3_node68_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,40] 4 profile3_node68_cert).mp (by decide +kernel))

def profile3_node71_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 41 50 7 24 24 40), lower := (rows 41 50 7 24 16 32), losses := [{ target := 4, region := (rows 9 2 4 8 0 41), good := (rows 41 34 39 41 0 32) }] }

theorem profile3_node71 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3,16] 4 :=
  cut_bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3,16] 4 profile3_node71_cert
    ((SmallCut.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3,16] 4 profile3_node71_cert).mp (by decide +kernel))

def profile3_node70_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node70 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3] 4 (by decide) (choices 1) [16] profile3_node70_route
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,3] (choices 1) [16] profile3_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node71

def profile3_node72_cert : Bound 6 := { allowed := (rows 16 8 48 0 0 0), upper := (rows 41 50 13 26 18 50), lower := (rows 41 50 13 8 16 32), losses := [] }

theorem profile3_node72 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,9] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,9] 4 profile3_node72_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,9] 4 profile3_node72_cert).mp (by decide +kernel))

def profile3_node73_cert : Bound 6 := { allowed := (rows 16 8 48 0 0 0), upper := (rows 41 50 14 25 17 49), lower := (rows 41 50 14 8 16 32), losses := [] }

theorem profile3_node73 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,10] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,10] 4 profile3_node73_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,10] 4 profile3_node73_cert).mp (by decide +kernel))

def profile3_node74_cert : Bound 6 := { allowed := (rows 16 8 40 0 0 0), upper := (rows 41 50 21 10 26 42), lower := (rows 41 50 21 8 16 32), losses := [] }

theorem profile3_node74 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,17] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,17] 4 profile3_node74_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,17] 4 profile3_node74_cert).mp (by decide +kernel))

def profile3_node75_cert : Bound 6 := { allowed := (rows 16 8 40 0 0 0), upper := (rows 41 50 22 9 25 41), lower := (rows 41 50 22 8 16 32), losses := [] }

theorem profile3_node75 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,18] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,18] 4 profile3_node75_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,18] 4 profile3_node75_cert).mp (by decide +kernel))

def profile3_node76_cert : Bound 6 := { allowed := (rows 16 8 32 0 0 0), upper := (rows 41 50 28 11 19 35), lower := (rows 41 50 28 8 16 32), losses := [] }

theorem profile3_node76 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,24] 4 :=
  bound_sound (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,24] 4 profile3_node76_cert
    ((SmallBoolean.boundCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48,24] 4 profile3_node76_cert).mp (by decide +kernel))

def profile3_node69_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node69 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48] 4 (by decide) (choices 2) [3,9,10,17,18,24] profile3_node69_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40,48] (choices 2) [3,9,10,17,18,24] profile3_node69_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node70
  · exact profile3_node72
  · exact profile3_node73
  · exact profile3_node74
  · exact profile3_node75
  · exact profile3_node76

def profile3_node49_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node49 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40] 4 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node49_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [40] (choices 2) [9,17,24,33,40,48] profile3_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node50
  · exact profile3_node51
  · exact profile3_node58
  · exact profile3_node67
  · exact profile3_node68
  · exact profile3_node69

def profile3_node0_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [] 4 := by
  apply routed_branch (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [] 4 (by decide) (choices 2) [10,24,34,40] profile3_node0_route
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [] (choices 2) [10,24,34,40] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node20
  · exact profile3_node37
  · exact profile3_node49

theorem profile3 : Upper (D (n:=6) [33,33,32,18,18,2]) (R (n:=6) [33,33,32,18,18,2]) [] 4 := profile3_node0

def catalogue : List (List Nat) := [[2,2,32,32,34,34],[2,2,32,33,33,34],[2,18,18,32,32,34],[2,18,18,32,33,33]]

theorem catalogue_eq : hardProfiles 6 8 4 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 6 8 4 true) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 4 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
theorem profile_upper (xs : List Nat) (member : xs∈profiles 6 true 6 0 8 8) :
    Upper (n:=6) (D xs.reverse) (R xs.reverse) [] 4 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 6)) (loops : Loopless E) (budget : arcCount E=8)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤4 := by
  have od (x) : SparseSupport.outdegree E x<6 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<6 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 6).map (SparseSupport.outdegree E)).sum=8 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 6).map (SparseSupport.indegree E)).sum=8 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetEightFinite6
