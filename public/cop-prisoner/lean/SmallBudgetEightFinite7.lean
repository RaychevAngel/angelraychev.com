import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
7 vertices with 8 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetEightFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g : Nat) : Rows 7 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64]
  | 2 => [3,5,9,17,33,65,6,10,18,34,66,12,20,36,68,24,40,72,48,80,96]
  | 3 => [7,11,19,35,67,13,21,37,69,25,41,73,49,81,97,14,22,38,70,26,42,74,50,82,98,28,44,76,52,84,100,56,88,104,112]
  | 4 => [15,23,39,71,27,43,75,51,83,99,29,45,77,53,85,101,57,89,105,113,30,46,78,54,86,102,58,90,106,114,60,92,108,116,120]
  | 5 => [31,47,79,55,87,103,59,91,107,115,61,93,109,117,121,62,94,110,118,122,124]
  | 6 => [63,95,111,119,123,125,126]
  | 7 => [127]
  | _ => []

theorem cover (d : Fin 8) : RowCover 7 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node2_cert : CutBound 7 := { lost := (rows 0 32 16 16 0 0 0), upper := (rows 49 19 101 105 113 97 97), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 67), good := (rows 109 111 4 8 0 32 64) },{ target := 5, region := (rows 1 3 4 8 16 0 64), good := (rows 19 19 4 8 16 0 64) }] }

theorem profile0_node2 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,17] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,17] 4 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,17] 4 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 49 50 69 73 81 97 65), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 64), good := (rows 50 50 4 8 16 32 64) },{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 34 4 8 0 32 64) }] }

theorem profile0_node3 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,48] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,48] 4 profile0_node3_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,48] 4 profile0_node3_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 49 67 21 104 112 96 96), lower := (rows 49 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 122 124 120 120 120 120) },{ target := 4, region := (rows 1 7 4 127 0 127 127), good := (rows 107 107 111 104 104 104 104) }] }

theorem profile0_node5 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,17] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,17] 4 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,17] 4 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 49 67 52 73 81 97 65), lower := (rows 49 67 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 64), good := (rows 52 70 52 8 16 32 64) },{ target := 4, region := (rows 1 3 4 11 0 35 67), good := (rows 107 107 36 8 0 32 64) }] }

theorem profile0_node6 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,48] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,48] 4 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,48] 4 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 67 69 56 48 48 112), lower := (rows 49 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 122 124 120 120 120 120) },{ target := 4, region := (rows 1 6 6 8 0 32 64), good := (rows 33 71 71 8 0 32 64) }] }

theorem profile0_node7 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,65] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,65] 4 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,65] 4 profile0_node7_cert).mp (by decide +kernel))

def profile0_node8_cert : CutBound 7 := { lost := (rows 64 16 0 80 0 0 0), upper := (rows 49 67 84 41 49 33 97), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 67), good := (rows 107 107 68 8 0 32 64) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile0_node8 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,80] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,80] 4 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65,80] 4 profile0_node8_cert).mp (by decide +kernel))

def profile0_node4_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node4 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65] 4 := by
  apply routed_branch (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65] 4 (by decide) (choices 2) [17,48,65,80] profile0_node4_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,65] (choices 2) [17,48,65,80] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7
  · exact profile0_node8

def profile0_node10_cert : CutBound 7 := { lost := (rows 0 32 16 48 0 0 0), upper := (rows 49 82 37 73 81 97 65), lower := (rows 49 82 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 13 0 37 69), good := (rows 109 66 109 8 0 32 64) },{ target := 5, region := (rows 1 7 4 13 21 0 69), good := (rows 91 82 95 8 16 0 64) }] }

theorem profile0_node10 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,33] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,33] 4 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,33] 4 profile0_node10_cert).mp (by decide +kernel))

def profile0_node11_cert : CutBound 7 := { lost := (rows 64 0 16 80 0 0 0), upper := (rows 49 82 69 41 49 33 97), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 13 0 37 69), good := (rows 109 66 109 8 0 32 64) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile0_node11 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,65] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,65] 4 profile0_node11_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,65] 4 profile0_node11_cert).mp (by decide +kernel))

def profile0_node12_cert : CutBound 7 := { lost := (rows 0 32 16 48 0 0 0), upper := (rows 49 82 100 9 17 33 65), lower := (rows 49 82 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 66 100 8 0 32 64) },{ target := 5, region := (rows 1 3 4 9 17 0 65), good := (rows 91 82 68 8 16 0 64) }] }

theorem profile0_node12 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,96] 4 :=
  cut_bound_sound (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,96] 4 profile0_node12_cert
    ((SmallCut.boundCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80,96] 4 profile0_node12_cert).mp (by decide +kernel))

def profile0_node9_route : Route 7 := (fun mask => (mask,id))

theorem profile0_node9 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80] 4 := by
  apply routed_branch (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80] 4 (by decide) (choices 2) [33,65,96] profile0_node9_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48,80] (choices 2) [33,65,96] profile0_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node10
  · exact profile0_node11
  · exact profile0_node12

def profile0_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48] 4 := by
  apply routed_branch (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48] 4 (by decide) (choices 2) [17,48,65,80] profile0_node1_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [48] (choices 2) [17,48,65,80] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4
  · exact profile0_node9

def profile0_node0_route : Route 7 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [] 4 := by
  apply routed_branch (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [] 4 (by decide) (choices 2) [48] profile0_node0_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [] (choices 2) [48] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=7) [34,32,32,32,2,2,2]) (R (n:=7) [34,32,32,32,2,2,2]) [] 4 := profile0_node0

def profile1_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 100 104 112 96 96), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 127 0 127 127), good := (rows 111 111 108 108 108 108 108) }] }

theorem profile1_node2 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,17] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,17] 4 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,17] 4 profile1_node2_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 52 72 80 96 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile1_node4 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,48] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,48] 4 profile1_node4_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,48] 4 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 84 104 112 96 96), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile1_node5 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,80] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,80] 4 profile1_node5_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,80] 4 profile1_node5_cert).mp (by decide +kernel))

def profile1_node6_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 19 35 100 88 80 112 80), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile1_node6 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,96] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,96] 4 profile1_node6_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33,96] 4 profile1_node6_cert).mp (by decide +kernel))

def profile1_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33] 4 (by decide) (choices 2) [48,80,96] profile1_node3_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,33] (choices 2) [48,80,96] profile1_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node4
  · exact profile1_node5
  · exact profile1_node6

def profile1_node7_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 101 105 113 97 97), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 111 34 4 8 0 32 64) }] }

theorem profile1_node7 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,48] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,48] 4 profile1_node7_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,48] 4 profile1_node7_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 21 104 112 96 96), lower := (rows 19 98 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 127 0 127 127), good := (rows 107 106 111 106 106 106 106) }] }

theorem profile1_node9 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,17] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,17] 4 profile1_node9_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,17] 4 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 19 98 37 88 80 112 80), lower := (rows 19 98 37 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 127 127 0 127), good := (rows 91 91 93 88 88 88 88) }] }

theorem profile1_node10 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,33] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,33] 4 profile1_node10_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,33] 4 profile1_node10_cert).mp (by decide +kernel))

def profile1_node11_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 52 73 81 97 65), lower := (rows 19 98 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 9 0 33 65), good := (rows 107 98 36 8 0 32 64) }] }

theorem profile1_node11 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,48] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,48] 4 profile1_node11_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,48] 4 profile1_node11_cert).mp (by decide +kernel))

def profile1_node12_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 98 100 25 17 49 81), lower := (rows 19 98 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 64), good := (rows 7 102 102 8 0 32 64) }] }

theorem profile1_node12 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,96] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,96] 4 profile1_node12_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96,96] 4 profile1_node12_cert).mp (by decide +kernel))

def profile1_node8_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node8 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96] 4 (by decide) (choices 2) [17,33,48,96] profile1_node8_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18,96] (choices 2) [17,33,48,96] profile1_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node9
  · exact profile1_node10
  · exact profile1_node11
  · exact profile1_node12

def profile1_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18] 4 (by decide) (choices 2) [17,33,48,96] profile1_node1_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [18] (choices 2) [17,33,48,96] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node7
  · exact profile1_node8

def profile1_node14_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 102 106 114 98 98), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 66), good := (rows 33 111 4 8 0 32 64) }] }

theorem profile1_node14 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,17] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,17] 4 profile1_node14_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,17] 4 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 49 50 71 75 83 99 67), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile1_node15 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,48] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,48] 4 profile1_node15_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,48] 4 profile1_node15_cert).mp (by decide +kernel))

def profile1_node17_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 67 22 104 112 96 96), lower := (rows 49 67 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 110 104 104 104 104) }] }

theorem profile1_node17 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,18] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,18] 4 profile1_node17_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,18] 4 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 67 52 74 82 98 66), lower := (rows 49 67 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 67), good := (rows 107 107 36 8 0 32 64) }] }

theorem profile1_node18 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,48] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,48] 4 profile1_node18_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,48] 4 profile1_node18_cert).mp (by decide +kernel))

def profile1_node19_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 49 67 70 56 48 48 112), lower := (rows 49 67 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 64), good := (rows 33 71 70 8 0 32 64) },{ target := 5, region := (rows 1 2 6 8 16 0 64), good := (rows 17 71 70 8 16 0 64) }] }

theorem profile1_node19 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,66] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,66] 4 profile1_node19_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,66] 4 profile1_node19_cert).mp (by decide +kernel))

def profile1_node20_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 67 84 42 50 34 98), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 67), good := (rows 107 107 68 8 0 32 64) }] }

theorem profile1_node20 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,80] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,80] 4 profile1_node20_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65,80] 4 profile1_node20_cert).mp (by decide +kernel))

def profile1_node16_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node16 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65] 4 (by decide) (choices 2) [18,48,66,80] profile1_node16_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,65] (choices 2) [18,48,66,80] profile1_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node17
  · exact profile1_node18
  · exact profile1_node19
  · exact profile1_node20

def profile1_node23_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 82 7 104 16 32 64), lower := (rows 49 82 7 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 106 111 104 104 104 104) },{ target := 5, region := (rows 1 127 5 8 127 0 127), good := (rows 87 82 87 90 82 82 82) }] }

theorem profile1_node23 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3,96] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3,96] 4 profile1_node23_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3,96] 4 profile1_node23_cert).mp (by decide +kernel))

def profile1_node22_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node22 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3] 4 (by decide) (choices 2) [96] profile1_node22_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,3] (choices 2) [96] profile1_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node23

def profile1_node24_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 82 37 74 82 98 66), lower := (rows 49 82 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 66), good := (rows 37 106 37 8 0 32 64) }] }

theorem profile1_node24 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,33] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,33] 4 profile1_node24_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,33] 4 profile1_node24_cert).mp (by decide +kernel))

def profile1_node25_cert : CutBound 7 := { lost := (rows 0 32 0 48 0 0 0), upper := (rows 49 82 38 73 81 97 65), lower := (rows 49 82 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 65), good := (rows 105 66 38 8 0 32 64) },{ target := 5, region := (rows 1 3 4 9 17 0 65), good := (rows 91 82 6 8 16 0 64) }] }

theorem profile1_node25 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,34] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,34] 4 profile1_node25_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,34] 4 profile1_node25_cert).mp (by decide +kernel))

def profile1_node26_cert : CutBound 7 := { lost := (rows 64 0 0 80 0 0 0), upper := (rows 49 82 69 42 50 34 98), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 66), good := (rows 33 106 69 8 0 32 64) },{ target := 6, region := (rows 3 2 4 10 18 34 0), good := (rows 49 59 5 8 16 32 0) }] }

theorem profile1_node26 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,65] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,65] 4 profile1_node26_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,65] 4 profile1_node26_cert).mp (by decide +kernel))

def profile1_node27_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 82 70 41 49 33 97), lower := (rows 49 82 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 65), good := (rows 105 70 70 8 0 32 64) }] }

theorem profile1_node27 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,66] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,66] 4 profile1_node27_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,66] 4 profile1_node27_cert).mp (by decide +kernel))

def profile1_node28_cert : CutBound 7 := { lost := (rows 0 32 0 32 0 0 0), upper := (rows 49 82 100 11 19 35 67), lower := (rows 49 82 100 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 9 17 0 65), good := (rows 91 82 68 8 16 0 64) }] }

theorem profile1_node28 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,96] 4 :=
  cut_bound_sound (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,96] 4 profile1_node28_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80,96] 4 profile1_node28_cert).mp (by decide +kernel))

def profile1_node21_route : Route 7 := (fun mask => (mask,id))

theorem profile1_node21 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80] 4 (by decide) (choices 2) [3,33,34,65,66,96] profile1_node21_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48,80] (choices 2) [3,33,34,65,66,96] profile1_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node22
  · exact profile1_node24
  · exact profile1_node25
  · exact profile1_node26
  · exact profile1_node27
  · exact profile1_node28

def profile1_node13_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node13 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48] 4 (by decide) (choices 2) [17,48,65,80] profile1_node13_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [48] (choices 2) [17,48,65,80] profile1_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node14
  · exact profile1_node15
  · exact profile1_node16
  · exact profile1_node21

def profile1_node0_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [] 4 := by
  apply routed_branch (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [] 4 (by decide) (choices 2) [18,48] profile1_node0_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [] (choices 2) [18,48] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node1
  · exact profile1_node13

theorem profile1 : Upper (D (n:=7) [33,33,32,32,2,2,2]) (R (n:=7) [33,33,32,32,2,2,2]) [] 4 := profile1_node0

def profile2_node2_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 11 100 104 112 96 96), lower := (rows 25 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 119 116 116 116 116 116) }] }

theorem profile2_node2 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,9] 4 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,9] 4 profile2_node2_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 35 44 72 80 96 64), lower := (rows 25 35 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile2_node4 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,40] 4 profile2_node4_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,40] 4 profile2_node4_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 35 76 104 112 96 96), lower := (rows 25 35 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile2_node5 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,72] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,72] 4 profile2_node5_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,72] 4 profile2_node5_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 35 100 72 88 104 72), lower := (rows 25 35 100 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile2_node6 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,96] 4 profile2_node6_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33,96] 4 profile2_node6_cert).mp (by decide +kernel))

def profile2_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node3 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33] 4 (by decide) (choices 2) [40,72,96] profile2_node3_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,33] (choices 2) [40,72,96] profile2_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node4
  · exact profile2_node5
  · exact profile2_node6

def profile2_node7_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 42 101 105 113 97 97), lower := (rows 25 42 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 34 4 0 16 32 64) }] }

theorem profile2_node7 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,40] 4 profile2_node7_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,40] 4 profile2_node7_cert).mp (by decide +kernel))

def profile2_node9_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 98 13 104 112 96 96), lower := (rows 25 98 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 119 114 114 114 114) }] }

theorem profile2_node9 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,9] 4 profile2_node9_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,9] 4 profile2_node9_cert).mp (by decide +kernel))

def profile2_node10_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 98 37 72 88 104 72), lower := (rows 25 98 37 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile2_node10 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,33] 4 profile2_node10_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,33] 4 profile2_node10_cert).mp (by decide +kernel))

def profile2_node11_cert : Bound 7 := { allowed := (rows 96 8 64 0 0 0 0), upper := (rows 25 98 44 73 81 97 65), lower := (rows 25 98 44 8 16 32 64), losses := [] }

theorem profile2_node11 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,40] 4 profile2_node11_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,40] 4 profile2_node11_cert).mp (by decide +kernel))

def profile2_node12_cert : Bound 7 := { allowed := (rows 96 8 8 0 0 0 0), upper := (rows 25 98 100 9 25 41 73), lower := (rows 25 98 100 8 16 32 64), losses := [] }

theorem profile2_node12 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,96] 4 profile2_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96,96] 4 profile2_node12_cert).mp (by decide +kernel))

def profile2_node8_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node8 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96] 4 (by decide) (choices 2) [9,33,40,96] profile2_node8_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24,96] (choices 2) [9,33,40,96] profile2_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node9
  · exact profile2_node10
  · exact profile2_node11
  · exact profile2_node12

def profile2_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24] 4 (by decide) (choices 2) [9,33,40,96] profile2_node1_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [24] (choices 2) [9,33,40,96] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node7
  · exact profile2_node8

def profile2_node14_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 41 11 116 120 112 112 112), lower := (rows 41 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 119 116 116 116 116 116) }] }

theorem profile2_node14 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,9] 4 profile2_node14_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,9] 4 profile2_node14_cert).mp (by decide +kernel))

def profile2_node16_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 41 19 44 72 80 96 64), lower := (rows 41 19 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile2_node16 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,40] 4 profile2_node16_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,40] 4 profile2_node16_cert).mp (by decide +kernel))

def profile2_node17_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 41 19 76 104 112 96 96), lower := (rows 41 19 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile2_node17 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,72] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,72] 4 profile2_node17_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,72] 4 profile2_node17_cert).mp (by decide +kernel))

def profile2_node18_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 41 19 100 72 88 104 72), lower := (rows 41 19 100 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node18 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,96] 4 profile2_node18_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17,96] 4 profile2_node18_cert).mp (by decide +kernel))

def profile2_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node15 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17] 4 (by decide) (choices 2) [40,72,96] profile2_node15_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,17] (choices 2) [40,72,96] profile2_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node16
  · exact profile2_node17
  · exact profile2_node18

def profile2_node19_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 41 26 101 105 113 97 97), lower := (rows 41 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 18 4 0 16 32 64) }] }

theorem profile2_node19 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,24] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,24] 4 profile2_node19_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,24] 4 profile2_node19_cert).mp (by decide +kernel))

def profile2_node20_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 41 35 92 88 88 120 88), lower := (rows 41 35 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64), good := (rows 35 35 4 0 16 32 64) }] }

theorem profile2_node20 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,33] 4 profile2_node20_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,33] 4 profile2_node20_cert).mp (by decide +kernel))

def profile2_node21_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 41 42 85 89 81 113 81), lower := (rows 41 42 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 34 4 0 16 32 64) }] }

theorem profile2_node21 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,40] 4 profile2_node21_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,40] 4 profile2_node21_cert).mp (by decide +kernel))

def profile2_node22_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 41 50 77 73 89 105 73), lower := (rows 41 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 18 4 8 16 0 64) }] }

theorem profile2_node22 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,48] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,48] 4 profile2_node22_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,48] 4 profile2_node22_cert).mp (by decide +kernel))

def profile2_node24_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 41 67 28 104 112 96 96), lower := (rows 41 67 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile2_node24 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,24] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,24] 4 profile2_node24_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,24] 4 profile2_node24_cert).mp (by decide +kernel))

def profile2_node25_cert : Bound 7 := { allowed := (rows 64 40 64 0 0 0 0), upper := (rows 41 67 44 88 80 112 80), lower := (rows 41 67 44 8 16 32 64), losses := [] }

theorem profile2_node25 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,40] 4 profile2_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,40] 4 profile2_node25_cert).mp (by decide +kernel))

def profile2_node26_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 41 67 52 72 88 104 72), lower := (rows 41 67 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node26 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,48] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,48] 4 profile2_node26_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,48] 4 profile2_node26_cert).mp (by decide +kernel))

def profile2_node27_cert : Bound 7 := { allowed := (rows 64 40 32 0 0 0 0), upper := (rows 41 67 76 56 48 48 112), lower := (rows 41 67 76 8 16 32 64), losses := [] }

theorem profile2_node27 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,72] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,72] 4 profile2_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,72] 4 profile2_node27_cert).mp (by decide +kernel))

def profile2_node28_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 41 67 84 40 56 40 104), lower := (rows 41 67 84 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile2_node28 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,80] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,80] 4 profile2_node28_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,80] 4 profile2_node28_cert).mp (by decide +kernel))

def profile2_node29_cert : Bound 7 := { allowed := (rows 64 40 8 0 0 0 0), upper := (rows 41 67 100 24 24 56 88), lower := (rows 41 67 100 8 16 32 64), losses := [] }

theorem profile2_node29 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,96] 4 profile2_node29_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65,96] 4 profile2_node29_cert).mp (by decide +kernel))

def profile2_node23_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node23 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65] 4 (by decide) (choices 2) [24,40,48,72,80,96] profile2_node23_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,65] (choices 2) [24,40,48,72,80,96] profile2_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node24
  · exact profile2_node25
  · exact profile2_node26
  · exact profile2_node27
  · exact profile2_node28
  · exact profile2_node29

def profile2_node30_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 41 74 117 121 113 113 113), lower := (rows 41 74 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 66 4 0 16 32 64) }] }

theorem profile2_node30 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,72] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,72] 4 profile2_node30_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,72] 4 profile2_node30_cert).mp (by decide +kernel))

def profile2_node32_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 41 82 13 104 112 96 96), lower := (rows 41 82 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 119 114 114 114 114) }] }

theorem profile2_node32 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,9] 4 profile2_node32_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,9] 4 profile2_node32_cert).mp (by decide +kernel))

def profile2_node33_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 41 82 37 72 88 104 72), lower := (rows 41 82 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 37 82 37 0 16 32 64) }] }

theorem profile2_node33 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,33] 4 profile2_node33_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,33] 4 profile2_node33_cert).mp (by decide +kernel))

def profile2_node34_cert : Bound 7 := { allowed := (rows 64 40 64 0 0 0 0), upper := (rows 41 82 44 73 81 97 65), lower := (rows 41 82 44 8 16 32 64), losses := [] }

theorem profile2_node34 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,40] 4 profile2_node34_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,40] 4 profile2_node34_cert).mp (by decide +kernel))

def profile2_node35_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 41 82 69 40 56 40 104), lower := (rows 41 82 69 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile2_node35 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,65] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,65] 4 profile2_node35_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,65] 4 profile2_node35_cert).mp (by decide +kernel))

def profile2_node36_cert : Bound 7 := { allowed := (rows 64 40 32 0 0 0 0), upper := (rows 41 82 76 41 49 33 97), lower := (rows 41 82 76 8 16 32 64), losses := [] }

theorem profile2_node36 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,72] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,72] 4 profile2_node36_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,72] 4 profile2_node36_cert).mp (by decide +kernel))

def profile2_node37_cert : Bound 7 := { allowed := (rows 64 40 8 0 0 0 0), upper := (rows 41 82 100 9 25 41 73), lower := (rows 41 82 100 8 16 32 64), losses := [] }

theorem profile2_node37 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,96] 4 profile2_node37_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80,96] 4 profile2_node37_cert).mp (by decide +kernel))

def profile2_node31_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node31 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80] 4 (by decide) (choices 2) [9,33,40,65,72,96] profile2_node31_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,80] (choices 2) [9,33,40,65,72,96] profile2_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node32
  · exact profile2_node33
  · exact profile2_node34
  · exact profile2_node35
  · exact profile2_node36
  · exact profile2_node37

def profile2_node38_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 41 98 93 89 89 121 89), lower := (rows 41 98 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 66 4 8 16 0 64) }] }

theorem profile2_node38 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,96] 4 profile2_node38_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40,96] 4 profile2_node38_cert).mp (by decide +kernel))

def profile2_node13_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node13 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40] 4 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile2_node13_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [40] (choices 2) [9,17,24,33,40,48,65,72,80,96] profile2_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node14
  · exact profile2_node15
  · exact profile2_node19
  · exact profile2_node20
  · exact profile2_node21
  · exact profile2_node22
  · exact profile2_node23
  · exact profile2_node30
  · exact profile2_node31
  · exact profile2_node38

def profile2_node41_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 49 11 44 72 80 96 64), lower := (rows 49 11 44 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) }] }

theorem profile2_node41 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,40] 4 profile2_node41_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,40] 4 profile2_node41_cert).mp (by decide +kernel))

def profile2_node42_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 49 11 76 104 112 96 96), lower := (rows 49 11 76 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) }] }

theorem profile2_node42 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,72] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,72] 4 profile2_node42_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,72] 4 profile2_node42_cert).mp (by decide +kernel))

def profile2_node43_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 11 100 72 88 104 72), lower := (rows 49 11 100 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node43 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,96] 4 profile2_node43_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9,96] 4 profile2_node43_cert).mp (by decide +kernel))

def profile2_node40_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node40 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9] 4 (by decide) (choices 2) [40,72,96] profile2_node40_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,9] (choices 2) [40,72,96] profile2_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node41
  · exact profile2_node42
  · exact profile2_node43

def profile2_node44_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 49 35 76 72 88 104 72), lower := (rows 49 35 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64), good := (rows 51 35 4 0 16 32 64) }] }

theorem profile2_node44 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,33] 4 profile2_node44_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,33] 4 profile2_node44_cert).mp (by decide +kernel))

def profile2_node45_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 49 42 77 73 89 105 73), lower := (rows 49 42 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 10 4 8 16 0 64) }] }

theorem profile2_node45 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,40] 4 profile2_node45_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,40] 4 profile2_node45_cert).mp (by decide +kernel))

def profile2_node47_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 67 44 72 88 104 72), lower := (rows 49 67 44 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node47 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,40] 4 profile2_node47_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,40] 4 profile2_node47_cert).mp (by decide +kernel))

def profile2_node48_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 49 67 76 40 56 40 104), lower := (rows 49 67 76 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile2_node48 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,72] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,72] 4 profile2_node48_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,72] 4 profile2_node48_cert).mp (by decide +kernel))

def profile2_node49_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 67 100 8 24 40 72), lower := (rows 49 67 100 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node49 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,96] 4 profile2_node49_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65,96] 4 profile2_node49_cert).mp (by decide +kernel))

def profile2_node46_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node46 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65] 4 (by decide) (choices 2) [40,72,96] profile2_node46_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,65] (choices 2) [40,72,96] profile2_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node47
  · exact profile2_node48
  · exact profile2_node49

def profile2_node51_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 49 74 13 104 112 96 96), lower := (rows 49 74 13 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) }] }

theorem profile2_node51 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,9] 4 profile2_node51_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,9] 4 profile2_node51_cert).mp (by decide +kernel))

def profile2_node52_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 49 74 37 72 88 104 72), lower := (rows 49 74 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 53 66 37 0 16 32 64) }] }

theorem profile2_node52 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,33] 4 profile2_node52_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,33] 4 profile2_node52_cert).mp (by decide +kernel))

def profile2_node53_cert : Bound 7 := { allowed := (rows 72 32 64 0 0 0 0), upper := (rows 49 74 44 73 81 97 65), lower := (rows 49 74 44 8 16 32 64), losses := [] }

theorem profile2_node53 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,40] 4 profile2_node53_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,40] 4 profile2_node53_cert).mp (by decide +kernel))

def profile2_node54_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 49 74 69 40 56 40 104), lower := (rows 49 74 69 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile2_node54 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,65] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,65] 4 profile2_node54_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,65] 4 profile2_node54_cert).mp (by decide +kernel))

def profile2_node55_cert : Bound 7 := { allowed := (rows 72 32 32 0 0 0 0), upper := (rows 49 74 76 41 49 33 97), lower := (rows 49 74 76 8 16 32 64), losses := [] }

theorem profile2_node55 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,72] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,72] 4 profile2_node55_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,72] 4 profile2_node55_cert).mp (by decide +kernel))

def profile2_node56_cert : Bound 7 := { allowed := (rows 72 32 8 0 0 0 0), upper := (rows 49 74 100 9 25 41 73), lower := (rows 49 74 100 8 16 32 64), losses := [] }

theorem profile2_node56 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,96] 4 profile2_node56_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72,96] 4 profile2_node56_cert).mp (by decide +kernel))

def profile2_node50_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node50 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72] 4 (by decide) (choices 2) [9,33,40,65,72,96] profile2_node50_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,72] (choices 2) [9,33,40,65,72,96] profile2_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node51
  · exact profile2_node52
  · exact profile2_node53
  · exact profile2_node54
  · exact profile2_node55
  · exact profile2_node56

def profile2_node57_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 49 98 77 73 89 105 73), lower := (rows 49 98 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 66 4 8 16 0 64) }] }

theorem profile2_node57 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,96] 4 profile2_node57_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48,96] 4 profile2_node57_cert).mp (by decide +kernel))

def profile2_node39_route : Route 7 := (fun mask => (mask,id))

theorem profile2_node39 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48] 4 (by decide) (choices 2) [9,33,40,65,72,96] profile2_node39_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [48] (choices 2) [9,33,40,65,72,96] profile2_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node40
  · exact profile2_node44
  · exact profile2_node45
  · exact profile2_node46
  · exact profile2_node50
  · exact profile2_node57

def profile2_node60_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 97 11 28 104 112 96 96), lower := (rows 97 11 28 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) }] }

theorem profile2_node60 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,24] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,24] 4 profile2_node60_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,24] 4 profile2_node60_cert).mp (by decide +kernel))

def profile2_node61_cert : Bound 7 := { allowed := (rows 8 96 64 0 0 0 0), upper := (rows 97 11 44 88 80 112 80), lower := (rows 97 11 44 8 16 32 64), losses := [] }

theorem profile2_node61 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,40] 4 profile2_node61_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,40] 4 profile2_node61_cert).mp (by decide +kernel))

def profile2_node62_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 97 11 52 72 88 104 72), lower := (rows 97 11 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node62 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,48] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,48] 4 profile2_node62_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,48] 4 profile2_node62_cert).mp (by decide +kernel))

def profile2_node63_cert : Bound 7 := { allowed := (rows 8 96 8 0 0 0 0), upper := (rows 97 11 100 24 24 56 88), lower := (rows 97 11 100 8 16 32 64), losses := [] }

theorem profile2_node63 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,96] 4 profile2_node63_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9,96] 4 profile2_node63_cert).mp (by decide +kernel))

def profile2_node59_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node59 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9] 4 (by decide) (choices 2) [24,40,48,96] profile2_node59_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,9] (choices 2) [24,40,48,96] profile2_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node60
  · exact profile2_node61
  · exact profile2_node62
  · exact profile2_node63

def profile2_node65_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 97 19 44 72 88 104 72), lower := (rows 97 19 44 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 91 91 92 88 88 88 88) }] }

theorem profile2_node65 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,40] 4 profile2_node65_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,40] 4 profile2_node65_cert).mp (by decide +kernel))

def profile2_node66_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 97 19 100 8 24 40 72), lower := (rows 97 19 100 8 16 32 64), losses := [{ target := 3, region := (rows 5 2 5 0 16 32 64), good := (rows 101 23 101 0 16 32 64) }] }

theorem profile2_node66 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,96] 4 profile2_node66_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17,96] 4 profile2_node66_cert).mp (by decide +kernel))

def profile2_node64_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node64 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17] 4 (by decide) (choices 2) [40,96] profile2_node64_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,17] (choices 2) [40,96] profile2_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node65
  · exact profile2_node66

def profile2_node68_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 97 26 13 104 112 96 96), lower := (rows 97 26 13 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) }] }

theorem profile2_node68 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,9] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,9] 4 profile2_node68_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,9] 4 profile2_node68_cert).mp (by decide +kernel))

def profile2_node69_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 97 26 37 72 88 104 72), lower := (rows 97 26 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 101 18 37 0 16 32 64) }] }

theorem profile2_node69 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,33] 4 profile2_node69_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,33] 4 profile2_node69_cert).mp (by decide +kernel))

def profile2_node70_cert : Bound 7 := { allowed := (rows 8 96 64 0 0 0 0), upper := (rows 97 26 44 73 81 97 65), lower := (rows 97 26 44 8 16 32 64), losses := [] }

theorem profile2_node70 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,40] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,40] 4 profile2_node70_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,40] 4 profile2_node70_cert).mp (by decide +kernel))

def profile2_node71_cert : Bound 7 := { allowed := (rows 8 96 8 0 0 0 0), upper := (rows 97 26 100 9 25 41 73), lower := (rows 97 26 100 8 16 32 64), losses := [] }

theorem profile2_node71 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,96] 4 :=
  bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,96] 4 profile2_node71_cert
    ((SmallBoolean.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24,96] 4 profile2_node71_cert).mp (by decide +kernel))

def profile2_node67_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node67 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24] 4 (by decide) (choices 2) [9,33,40,96] profile2_node67_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,24] (choices 2) [9,33,40,96] profile2_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node68
  · exact profile2_node69
  · exact profile2_node70
  · exact profile2_node71

def profile2_node72_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 97 35 92 88 88 120 88), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64), good := (rows 99 35 4 0 16 32 64) }] }

theorem profile2_node72 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,33] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,33] 4 profile2_node72_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,33] 4 profile2_node72_cert).mp (by decide +kernel))

def profile2_node73_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 97 42 93 89 89 121 89), lower := (rows 97 42 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 10 4 8 16 0 64) }] }

theorem profile2_node73 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,40] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,40] 4 profile2_node73_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,40] 4 profile2_node73_cert).mp (by decide +kernel))

def profile2_node74_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 97 50 77 73 89 105 73), lower := (rows 97 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 65), good := (rows 93 18 4 8 16 0 64) }] }

theorem profile2_node74 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,48] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,48] 4 profile2_node74_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,48] 4 profile2_node74_cert).mp (by decide +kernel))

def profile2_node75_cert : CutBound 7 := { lost := (rows 8 8 0 0 0 0 0), upper := (rows 97 98 29 25 25 57 89), lower := (rows 97 98 4 8 16 32 64), losses := [{ target := 3, region := (rows 3 3 4 0 16 32 64), good := (rows 99 99 4 0 16 32 64) }] }

theorem profile2_node75 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,96] 4 :=
  cut_bound_sound (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,96] 4 profile2_node75_cert
    ((SmallCut.boundCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96,96] 4 profile2_node75_cert).mp (by decide +kernel))

def profile2_node58_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node58 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96] 4 (by decide) (choices 2) [9,17,24,33,40,48,96] profile2_node58_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [96] (choices 2) [9,17,24,33,40,48,96] profile2_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node59
  · exact profile2_node64
  · exact profile2_node67
  · exact profile2_node72
  · exact profile2_node73
  · exact profile2_node74
  · exact profile2_node75

def profile2_node0_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [] 4 := by
  apply routed_branch (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [] 4 (by decide) (choices 2) [24,40,48,96] profile2_node0_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [] (choices 2) [24,40,48,96] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node1
  · exact profile2_node13
  · exact profile2_node39
  · exact profile2_node58

theorem profile2 : Upper (D (n:=7) [33,32,32,18,17,2,2]) (R (n:=7) [33,32,32,18,17,2,2]) [] 4 := profile2_node0

def profile3_node2_cert : CutBound 7 := { lost := (rows 0 0 24 0 0 0 0), upper := (rows 25 26 100 104 112 96 96), lower := (rows 25 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 1 2 127 127 0 127 127), good := (rows 109 110 108 108 108 108 108) }] }

theorem profile3_node2 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,24] 4 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,24] 4 profile3_node2_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 42 52 72 80 96 64), lower := (rows 25 42 52 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 1 127 4 127 0 127 127), good := (rows 107 106 110 106 106 106 106) }] }

theorem profile3_node4 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,48] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,48] 4 profile3_node4_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,48] 4 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 42 84 104 112 96 96), lower := (rows 25 42 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 1 127 4 127 0 127 127), good := (rows 107 106 110 106 106 106 106) }] }

theorem profile3_node5 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,80] 4 profile3_node5_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,80] 4 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 7 := { lost := (rows 32 0 8 0 0 0 0), upper := (rows 25 42 100 88 80 112 80), lower := (rows 25 42 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile3_node6 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,96] 4 profile3_node6_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40,96] 4 profile3_node6_cert).mp (by decide +kernel))

def profile3_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40] 4 (by decide) (choices 2) [48,80,96] profile3_node3_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,40] (choices 2) [48,80,96] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6

def profile3_node8_cert : CutBound 7 := { lost := (rows 0 24 0 0 0 0 0), upper := (rows 25 98 28 104 112 96 96), lower := (rows 25 98 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 4, region := (rows 1 127 4 127 0 127 127), good := (rows 107 106 110 106 106 106 106) }] }

theorem profile3_node8 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,24] 4 profile3_node8_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,24] 4 profile3_node8_cert).mp (by decide +kernel))

def profile3_node9_cert : CutBound 7 := { lost := (rows 32 8 0 0 0 0 0), upper := (rows 25 98 44 88 80 112 80), lower := (rows 25 98 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile3_node9 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,40] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,40] 4 profile3_node9_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,40] 4 profile3_node9_cert).mp (by decide +kernel))

def profile3_node10_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 25 98 100 24 24 56 88), lower := (rows 25 98 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64), good := (rows 17 102 102 0 16 32 64) }] }

theorem profile3_node10 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,96] 4 profile3_node10_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96,96] 4 profile3_node10_cert).mp (by decide +kernel))

def profile3_node7_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node7 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96] 4 (by decide) (choices 2) [24,40,96] profile3_node7_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24,96] (choices 2) [24,40,96] profile3_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node8
  · exact profile3_node9
  · exact profile3_node10

def profile3_node1_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node1 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24] 4 (by decide) (choices 2) [24,40,96] profile3_node1_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [24] (choices 2) [24,40,96] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node3
  · exact profile3_node7

def profile3_node13_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 41 26 52 72 80 96 64), lower := (rows 41 26 52 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) }] }

theorem profile3_node13 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,48] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,48] 4 profile3_node13_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,48] 4 profile3_node13_cert).mp (by decide +kernel))

def profile3_node14_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 41 26 84 104 112 96 96), lower := (rows 41 26 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) }] }

theorem profile3_node14 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,80] 4 profile3_node14_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,80] 4 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 7 := { lost := (rows 0 32 8 0 0 0 0), upper := (rows 41 26 100 88 80 112 80), lower := (rows 41 26 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) }] }

theorem profile3_node15 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,96] 4 profile3_node15_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24,96] 4 profile3_node15_cert).mp (by decide +kernel))

def profile3_node12_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node12 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24] 4 (by decide) (choices 2) [48,80,96] profile3_node12_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,24] (choices 2) [48,80,96] profile3_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node13
  · exact profile3_node14
  · exact profile3_node15

def profile3_node16_cert : CutBound 7 := { lost := (rows 16 16 8 0 0 0 0), upper := (rows 41 42 84 88 80 112 80), lower := (rows 41 42 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 4, region := (rows 3 3 4 8 0 32 64), good := (rows 43 43 4 8 0 32 64) }] }

theorem profile3_node16 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,40] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,40] 4 profile3_node16_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,40] 4 profile3_node16_cert).mp (by decide +kernel))

def profile3_node18_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 41 50 28 72 80 96 64), lower := (rows 41 50 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) }] }

theorem profile3_node18 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,24] 4 profile3_node18_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,24] 4 profile3_node18_cert).mp (by decide +kernel))

def profile3_node19_cert : CutBound 7 := { lost := (rows 0 8 32 0 0 0 0), upper := (rows 41 50 76 88 80 112 80), lower := (rows 41 50 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node19 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,72] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,72] 4 profile3_node19_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,72] 4 profile3_node19_cert).mp (by decide +kernel))

def profile3_node20_cert : CutBound 7 := { lost := (rows 16 0 32 0 0 0 0), upper := (rows 41 50 84 72 88 104 72), lower := (rows 41 50 84 8 16 32 64), losses := [{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node20 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,80] 4 profile3_node20_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48,80] 4 profile3_node20_cert).mp (by decide +kernel))

def profile3_node17_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node17 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48] 4 (by decide) (choices 2) [24,72,80] profile3_node17_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,48] (choices 2) [24,72,80] profile3_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node18
  · exact profile3_node19
  · exact profile3_node20

def profile3_node22_cert : CutBound 7 := { lost := (rows 0 32 8 0 0 0 0), upper := (rows 41 74 52 88 80 112 80), lower := (rows 41 74 52 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) }] }

theorem profile3_node22 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,48] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,48] 4 profile3_node22_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,48] 4 profile3_node22_cert).mp (by decide +kernel))

def profile3_node23_cert : CutBound 7 := { lost := (rows 64 0 8 0 0 0 0), upper := (rows 41 74 84 56 48 48 112), lower := (rows 41 74 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile3_node23 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,80] 4 profile3_node23_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,80] 4 profile3_node23_cert).mp (by decide +kernel))

def profile3_node24_cert : CutBound 7 := { lost := (rows 0 32 8 0 0 0 0), upper := (rows 41 74 100 24 16 48 80), lower := (rows 41 74 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 117 118 116 116 116 116 116) },{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) }] }

theorem profile3_node24 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,96] 4 profile3_node24_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72,96] 4 profile3_node24_cert).mp (by decide +kernel))

def profile3_node21_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node21 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72] 4 (by decide) (choices 2) [48,80,96] profile3_node21_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,72] (choices 2) [48,80,96] profile3_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node22
  · exact profile3_node23
  · exact profile3_node24

def profile3_node26_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 41 82 28 104 112 96 96), lower := (rows 41 82 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) }] }

theorem profile3_node26 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,24] 4 profile3_node26_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,24] 4 profile3_node26_cert).mp (by decide +kernel))

def profile3_node27_cert : CutBound 7 := { lost := (rows 16 8 16 0 0 0 0), upper := (rows 41 82 44 88 80 112 80), lower := (rows 41 82 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 4, region := (rows 5 2 5 8 0 32 64), good := (rows 45 66 45 8 0 32 64) }] }

theorem profile3_node27 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,40] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,40] 4 profile3_node27_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,40] 4 profile3_node27_cert).mp (by decide +kernel))

def profile3_node28_cert : CutBound 7 := { lost := (rows 16 32 0 0 0 0 0), upper := (rows 41 82 52 72 88 104 72), lower := (rows 41 82 52 8 16 32 64), losses := [{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) },{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) }] }

theorem profile3_node28 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,48] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,48] 4 profile3_node28_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,48] 4 profile3_node28_cert).mp (by decide +kernel))

def profile3_node29_cert : CutBound 7 := { lost := (rows 64 8 0 0 0 0 0), upper := (rows 41 82 76 56 48 48 112), lower := (rows 41 82 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile3_node29 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,72] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,72] 4 profile3_node29_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,72] 4 profile3_node29_cert).mp (by decide +kernel))

def profile3_node30_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 41 82 84 40 56 40 104), lower := (rows 41 82 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64), good := (rows 33 86 86 0 16 32 64) }] }

theorem profile3_node30 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,80] 4 profile3_node30_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,80] 4 profile3_node30_cert).mp (by decide +kernel))

def profile3_node31_cert : CutBound 7 := { lost := (rows 64 32 0 0 0 0 0), upper := (rows 41 82 100 24 24 56 88), lower := (rows 41 82 100 8 16 32 64), losses := [{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile3_node31 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,96] 4 profile3_node31_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80,96] 4 profile3_node31_cert).mp (by decide +kernel))

def profile3_node25_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node25 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80] 4 (by decide) (choices 2) [24,40,48,72,80,96] profile3_node25_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,80] (choices 2) [24,40,48,72,80,96] profile3_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node26
  · exact profile3_node27
  · exact profile3_node28
  · exact profile3_node29
  · exact profile3_node30
  · exact profile3_node31

def profile3_node33_cert : CutBound 7 := { lost := (rows 0 8 32 0 0 0 0), upper := (rows 41 98 28 88 80 112 80), lower := (rows 41 98 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node33 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,24] 4 profile3_node33_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,24] 4 profile3_node33_cert).mp (by decide +kernel))

def profile3_node34_cert : CutBound 7 := { lost := (rows 0 8 32 0 0 0 0), upper := (rows 41 98 76 24 16 48 80), lower := (rows 41 98 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 118 114 114 114 114) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node34 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,72] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,72] 4 profile3_node34_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,72] 4 profile3_node34_cert).mp (by decide +kernel))

def profile3_node35_cert : CutBound 7 := { lost := (rows 64 0 32 0 0 0 0), upper := (rows 41 98 84 24 24 56 88), lower := (rows 41 98 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) },{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile3_node35 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,80] 4 profile3_node35_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96,80] 4 profile3_node35_cert).mp (by decide +kernel))

def profile3_node32_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node32 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96] 4 (by decide) (choices 2) [24,72,80] profile3_node32_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40,96] (choices 2) [24,72,80] profile3_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node33
  · exact profile3_node34
  · exact profile3_node35

def profile3_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node11 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40] 4 (by decide) (choices 2) [24,40,48,72,80,96] profile3_node11_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [40] (choices 2) [24,40,48,72,80,96] profile3_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node12
  · exact profile3_node16
  · exact profile3_node17
  · exact profile3_node21
  · exact profile3_node25
  · exact profile3_node32

def profile3_node38_cert : CutBound 7 := { lost := (rows 24 0 0 0 0 0 0), upper := (rows 97 26 28 104 112 96 96), lower := (rows 97 26 28 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) },{ target := 4, region := (rows 127 2 4 127 0 127 127), good := (rows 105 107 109 105 105 105 105) }] }

theorem profile3_node38 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,24] 4 profile3_node38_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,24] 4 profile3_node38_cert).mp (by decide +kernel))

def profile3_node39_cert : CutBound 7 := { lost := (rows 8 32 0 0 0 0 0), upper := (rows 97 26 44 88 80 112 80), lower := (rows 97 26 44 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) },{ target := 5, region := (rows 1 127 4 127 127 0 127), good := (rows 91 90 94 90 90 90 90) }] }

theorem profile3_node39 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,40] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,40] 4 profile3_node39_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,40] 4 profile3_node39_cert).mp (by decide +kernel))

def profile3_node40_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 97 26 100 24 24 56 88), lower := (rows 97 26 100 8 16 32 64), losses := [{ target := 3, region := (rows 5 2 5 0 16 32 64), good := (rows 101 18 101 0 16 32 64) }] }

theorem profile3_node40 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,96] 4 profile3_node40_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24,96] 4 profile3_node40_cert).mp (by decide +kernel))

def profile3_node37_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node37 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24] 4 (by decide) (choices 2) [24,40,96] profile3_node37_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,24] (choices 2) [24,40,96] profile3_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node38
  · exact profile3_node39
  · exact profile3_node40

def profile3_node42_cert : CutBound 7 := { lost := (rows 8 0 32 0 0 0 0), upper := (rows 97 42 28 88 80 112 80), lower := (rows 97 42 28 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node42 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,24] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,24] 4 profile3_node42_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,24] 4 profile3_node42_cert).mp (by decide +kernel))

def profile3_node43_cert : CutBound 7 := { lost := (rows 8 0 32 0 0 0 0), upper := (rows 97 42 76 24 16 48 80), lower := (rows 97 42 76 8 16 32 64), losses := [{ target := 3, region := (rows 127 2 4 0 127 127 127), good := (rows 113 115 117 113 113 113 113) },{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) }] }

theorem profile3_node43 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,72] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,72] 4 profile3_node43_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,72] 4 profile3_node43_cert).mp (by decide +kernel))

def profile3_node44_cert : CutBound 7 := { lost := (rows 0 64 32 0 0 0 0), upper := (rows 97 42 84 24 24 56 88), lower := (rows 97 42 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 127 127 127 0 127), good := (rows 93 94 92 92 92 92 92) },{ target := 6, region := (rows 1 127 4 127 127 127 0), good := (rows 59 58 62 58 58 58 58) }] }

theorem profile3_node44 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,80] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,80] 4 profile3_node44_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40,80] 4 profile3_node44_cert).mp (by decide +kernel))

def profile3_node41_route : Route 7 := (fun mask => (mask,id))

theorem profile3_node41 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40] 4 (by decide) (choices 2) [24,72,80] profile3_node41_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,40] (choices 2) [24,72,80] profile3_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node42
  · exact profile3_node43
  · exact profile3_node44

def profile3_node45_cert : CutBound 7 := { lost := (rows 8 8 0 0 0 0 0), upper := (rows 97 98 28 24 24 56 88), lower := (rows 97 98 4 8 16 32 64), losses := [{ target := 3, region := (rows 3 3 4 0 16 32 64), good := (rows 99 99 4 0 16 32 64) }] }

theorem profile3_node45 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,96] 4 :=
  cut_bound_sound (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,96] 4 profile3_node45_cert
    ((SmallCut.boundCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96,96] 4 profile3_node45_cert).mp (by decide +kernel))

def profile3_node36_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node36 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96] 4 (by decide) (choices 2) [24,40,96] profile3_node36_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [96] (choices 2) [24,40,96] profile3_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node37
  · exact profile3_node41
  · exact profile3_node45

def profile3_node0_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [] 4 := by
  apply routed_branch (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [] 4 (by decide) (choices 2) [24,40,96] profile3_node0_route
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [] (choices 2) [24,40,96] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node11
  · exact profile3_node36

theorem profile3 : Upper (D (n:=7) [32,32,32,18,18,2,2]) (R (n:=7) [32,32,32,18,18,2,2]) [] 4 := profile3_node0

def catalogue : List (List Nat) := [[2,2,2,32,32,32,34],[2,2,2,32,32,33,33],[2,2,17,18,32,32,33],[2,2,18,18,32,32,32]]

theorem catalogue_eq : hardProfiles 7 8 4 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 7 8 4 true) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 4 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
theorem profile_upper (xs : List Nat) (member : xs∈profiles 7 true 7 0 8 8) :
    Upper (n:=7) (D xs.reverse) (R xs.reverse) [] 4 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 7)) (loops : Loopless E) (budget : arcCount E=8)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤4 := by
  have od (x) : SparseSupport.outdegree E x<7 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<7 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 7).map (SparseSupport.outdegree E)).sum=8 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 7).map (SparseSupport.indegree E)).sum=8 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetEightFinite7
