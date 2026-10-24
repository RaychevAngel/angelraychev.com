import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile24_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 103 107 115 99 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) }] }

theorem profile24_node2 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,17] 6 99 profile24_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,17] 6 99 profile24_node2_cert).mp (by decide +kernel))

def profile24_node4_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 19 35 7 89 81 113 64), lower := (rows 19 35 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 15 23 39 127), good := (rows 121 121 125 72 80 96 64) }] }

theorem profile24_node4 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,3] 6 81 profile24_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,3] 6 81 profile24_node4_cert).mp (by decide +kernel))

def profile24_node5_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 19 35 21 75 83 99 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 101 85 72 80 96 64) }] }

theorem profile24_node5 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,17] 6 67 profile24_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,17] 6 67 profile24_node5_cert).mp (by decide +kernel))

def profile24_node6_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 22 73 81 97 64), lower := (rows 19 35 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 102 86 72 80 96 64) }] }

theorem profile24_node6 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,18] 6 65 profile24_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,18] 6 65 profile24_node6_cert).mp (by decide +kernel))

def profile24_node7_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 19 35 69 91 83 115 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 101 69 72 80 96 64) }] }

theorem profile24_node7 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,65] 6 83 profile24_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,65] 6 83 profile24_node7_cert).mp (by decide +kernel))

def profile24_node8_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 70 89 81 113 64), lower := (rows 19 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 102 70 72 80 96 64) }] }

theorem profile24_node8 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,66] 6 81 profile24_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,66] 6 81 profile24_node8_cert).mp (by decide +kernel))

def profile24_node9_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 84 75 83 99 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) }] }

theorem profile24_node9 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,80] 6 67 profile24_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33,80] 6 67 profile24_node9_cert).mp (by decide +kernel))

def profile24_node3_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile24_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node3 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile24_node3_route profile24_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node4
  · exact profile24_node5
  · exact profile24_node6
  · exact profile24_node7
  · exact profile24_node8
  · exact profile24_node9

def profile24_node10_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 71 75 83 99 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) }] }

theorem profile24_node10 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,48] 6 67 profile24_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,48] 6 67 profile24_node10_cert).mp (by decide +kernel))

def profile24_node11_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 67 119 123 115 115 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile24_node11 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,65] 6 115 profile24_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,65] 6 115 profile24_node11_cert).mp (by decide +kernel))

def profile24_node12_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 82 103 107 115 99 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) }] }

theorem profile24_node12 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,80] 6 99 profile24_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,80] 6 99 profile24_node12_cert).mp (by decide +kernel))

def profile24_node13_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 98 87 91 83 115 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) }] }

theorem profile24_node13 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,96] 6 83 profile24_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18,96] 6 83 profile24_node13_cert).mp (by decide +kernel))

def profile24_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile24_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile24_node1_route profile24_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node2
  · exact profile24_node3
  · exact profile24_node10
  · exact profile24_node11
  · exact profile24_node12
  · exact profile24_node13

def profile24_node16_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 35 19 7 89 81 113 64), lower := (rows 35 19 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 15 23 39 127), good := (rows 121 121 125 72 80 96 64) }] }

theorem profile24_node16 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,3] 6 81 profile24_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,3] 6 81 profile24_node16_cert).mp (by decide +kernel))

def profile24_node17_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 35 19 21 75 83 99 64), lower := (rows 35 19 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 101 85 85 72 80 96 64) }] }

theorem profile24_node17 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,17] 6 67 profile24_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,17] 6 67 profile24_node17_cert).mp (by decide +kernel))

def profile24_node18_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 22 73 81 97 64), lower := (rows 35 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 102 86 86 72 80 96 64) }] }

theorem profile24_node18 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,18] 6 65 profile24_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,18] 6 65 profile24_node18_cert).mp (by decide +kernel))

def profile24_node19_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 35 19 69 91 83 115 64), lower := (rows 35 19 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 101 85 69 72 80 96 64) }] }

theorem profile24_node19 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,65] 6 83 profile24_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,65] 6 83 profile24_node19_cert).mp (by decide +kernel))

def profile24_node20_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 70 89 81 113 64), lower := (rows 35 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 102 86 70 72 80 96 64) }] }

theorem profile24_node20 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,66] 6 81 profile24_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,66] 6 81 profile24_node20_cert).mp (by decide +kernel))

def profile24_node21_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 84 75 83 99 64), lower := (rows 35 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 102 86 84 72 84 96 64) }] }

theorem profile24_node21 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,80] 6 67 profile24_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17,80] 6 67 profile24_node21_cert).mp (by decide +kernel))

def profile24_node15_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile24_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node15 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,17] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile24_node15_route profile24_node15_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node16
  · exact profile24_node17
  · exact profile24_node18
  · exact profile24_node19
  · exact profile24_node20
  · exact profile24_node21

def profile24_node22_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 67 87 91 83 115 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile24_node22 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,65] 6 83 profile24_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,65] 6 83 profile24_node22_cert).mp (by decide +kernel))

def profile24_node23_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 82 87 91 83 115 64), lower := (rows 35 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 98 82 68 72 82 96 64) }] }

theorem profile24_node23 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,80] 6 83 profile24_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34,80] 6 83 profile24_node23_cert).mp (by decide +kernel))

def profile24_node14_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile24_node14_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node14 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [34] 6 (by decide) (choices 2) [17,65,80] profile24_node14_route profile24_node14_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node15
  · exact profile24_node22
  · exact profile24_node23

def profile24_node25_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 71 75 83 99 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) }] }

theorem profile24_node25 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,17] 6 67 profile24_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,17] 6 67 profile24_node25_cert).mp (by decide +kernel))

def profile24_node26_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 87 91 83 115 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) }] }

theorem profile24_node26 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,65] 6 83 profile24_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,65] 6 83 profile24_node26_cert).mp (by decide +kernel))

def profile24_node27_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 82 71 75 83 99 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 68 72 82 96 64) }] }

theorem profile24_node27 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,80] 6 67 profile24_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48,80] 6 67 profile24_node27_cert).mp (by decide +kernel))

def profile24_node24_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile24_node24_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node24 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [48] 6 (by decide) (choices 2) [17,65,80] profile24_node24_route profile24_node24_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node25
  · exact profile24_node26
  · exact profile24_node27

def profile24_node28_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 67 115 119 123 115 115 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile24_node28 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [66] 6 115 profile24_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [66] 6 115 profile24_node28_cert).mp (by decide +kernel))

def profile24_node29_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 81 115 119 123 115 115 64), lower := (rows 81 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 64 68 72 81 96 64) }] }

theorem profile24_node29 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [80] 6 115 profile24_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [80] 6 115 profile24_node29_cert).mp (by decide +kernel))

def profile24_node30_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 97 83 87 91 83 115 64), lower := (rows 97 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 33 0 4 8 16 32 127), good := (rows 97 64 68 72 80 97 64) }] }

theorem profile24_node30 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [96] 6 83 profile24_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [96] 6 83 profile24_node30_cert).mp (by decide +kernel))

def profile24_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile24_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile24_node0_route profile24_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile24_node1
  · exact profile24_node14
  · exact profile24_node24
  · exact profile24_node28
  · exact profile24_node29
  · exact profile24_node30

theorem profile24 : Upper (D (n:=7) [35,34,32,32,18,17,2]) (R (n:=7) [35,34,32,32,18,17,2]) [] 6 := profile24_node0


#print axioms profile24
end Delivery.SmallBudgetTenFinite7
