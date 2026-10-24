import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile31_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 101 105 113 97 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) }] }

theorem profile31_node2 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,17] 6 97 profile31_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,17] 6 97 profile31_node2_cert).mp (by decide +kernel))

def profile31_node4_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 21 105 113 97 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile31_node4 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,17] 6 97 profile31_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,17] 6 97 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 35 37 89 81 113 64), lower := (rows 19 35 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 71 103 103 72 64 96 64) }] }

theorem profile31_node5 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,33] 6 81 profile31_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,33] 6 81 profile31_node5_cert).mp (by decide +kernel))

def profile31_node6_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 52 73 81 97 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) }] }

theorem profile31_node6 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,48] 6 65 profile31_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,48] 6 65 profile31_node6_cert).mp (by decide +kernel))

def profile31_node7_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 35 69 121 113 113 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 1 2 7 8 16 0 127), good := (rows 87 71 69 72 80 64 64) }] }

theorem profile31_node7 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,65] 6 113 profile31_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,65] 6 113 profile31_node7_cert).mp (by decide +kernel))

def profile31_node8_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 19 35 84 105 113 97 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile31_node8 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,80] 6 97 profile31_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,80] 6 97 profile31_node8_cert).mp (by decide +kernel))

def profile31_node9_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 19 35 100 89 81 113 64), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 86 102 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) }] }

theorem profile31_node9 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,96] 6 81 profile31_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33,96] 6 81 profile31_node9_cert).mp (by decide +kernel))

def profile31_node3_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile31_node3 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,33] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile31_node3_route profile31_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node4
  · exact profile31_node5
  · exact profile31_node6
  · exact profile31_node7
  · exact profile31_node8
  · exact profile31_node9

def profile31_node10_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 101 105 113 97 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) }] }

theorem profile31_node10 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,48] 6 97 profile31_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,48] 6 97 profile31_node10_cert).mp (by decide +kernel))

def profile31_node11_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 19 67 117 121 113 113 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile31_node11 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,65] 6 113 profile31_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,65] 6 113 profile31_node11_cert).mp (by decide +kernel))

def profile31_node12_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 19 82 101 105 113 97 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 66 68 72 64 96 64) }] }

theorem profile31_node12 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,80] 6 97 profile31_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,80] 6 97 profile31_node12_cert).mp (by decide +kernel))

def profile31_node13_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 19 98 117 121 113 113 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile31_node13 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,96] 6 113 profile31_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18,96] 6 113 profile31_node13_cert).mp (by decide +kernel))

def profile31_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile31_node1 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile31_node1_route profile31_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node2
  · exact profile31_node3
  · exact profile31_node10
  · exact profile31_node11
  · exact profile31_node12
  · exact profile31_node13

def profile31_node15_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 103 107 115 99 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) }] }

theorem profile31_node15 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,17] 6 99 profile31_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,17] 6 99 profile31_node15_cert).mp (by decide +kernel))

def profile31_node16_cert : CutBound 7 := { lost := (rows 64 65 0 0 0 0 0), upper := (rows 49 50 71 75 83 99 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 114 114 68 72 80 96 64) },{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile31_node16 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,48] 6 67 profile31_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,48] 6 67 profile31_node16_cert).mp (by decide +kernel))

def profile31_node17_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 49 67 119 123 115 115 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile31_node17 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,65] 6 115 profile31_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,65] 6 115 profile31_node17_cert).mp (by decide +kernel))

def profile31_node18_cert : CutBound 7 := { lost := (rows 0 33 0 0 0 0 0), upper := (rows 49 82 103 107 115 99 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 68 72 82 96 64) },{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 68 72 82 64 64) }] }

theorem profile31_node18 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,80] 6 99 profile31_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48,80] 6 99 profile31_node18_cert).mp (by decide +kernel))

def profile31_node14_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node14_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node14 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [48] 6 (by decide) (choices 2) [17,48,65,80] profile31_node14_route profile31_node14_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node15
  · exact profile31_node16
  · exact profile31_node17
  · exact profile31_node18

def profile31_node19_cert : CutBound 7 := { lost := (rows 48 0 0 0 0 0 0), upper := (rows 67 115 117 121 113 113 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) }] }

theorem profile31_node19 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [66] 6 113 profile31_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [66] 6 113 profile31_node19_cert).mp (by decide +kernel))

def profile31_node21_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 19 103 107 115 99 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) }] }

theorem profile31_node21 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,17] 6 99 profile31_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,17] 6 99 profile31_node21_cert).mp (by decide +kernel))

def profile31_node23_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 35 7 121 113 113 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 71 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 71 72 81 64 64) }] }

theorem profile31_node23 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,3] 6 113 profile31_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,3] 6 113 profile31_node23_cert).mp (by decide +kernel))

def profile31_node24_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 35 21 107 115 99 64), lower := (rows 81 35 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile31_node24 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,17] 6 99 profile31_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,17] 6 99 profile31_node24_cert).mp (by decide +kernel))

def profile31_node25_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 35 22 105 113 97 64), lower := (rows 81 35 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 110 72 64 96 64) }] }

theorem profile31_node25 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,18] 6 97 profile31_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,18] 6 97 profile31_node25_cert).mp (by decide +kernel))

def profile31_node26_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 35 37 91 83 115 64), lower := (rows 81 35 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 65 103 103 72 64 96 64) }] }

theorem profile31_node26 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,33] 6 83 profile31_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,33] 6 83 profile31_node26_cert).mp (by decide +kernel))

def profile31_node27_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 38 89 81 113 64), lower := (rows 81 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 102 72 64 96 64) }] }

theorem profile31_node27 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,34] 6 81 profile31_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,34] 6 81 profile31_node27_cert).mp (by decide +kernel))

def profile31_node28_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 35 52 75 83 99 64), lower := (rows 81 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) }] }

theorem profile31_node28 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,48] 6 67 profile31_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,48] 6 67 profile31_node28_cert).mp (by decide +kernel))

def profile31_node29_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 35 69 59 51 51 64), lower := (rows 81 35 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 69 103 69 72 64 96 64) },{ target := 5, region := (rows 17 2 23 8 16 0 127), good := (rows 85 71 69 72 85 64 64) }] }

theorem profile31_node29 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,65] 6 51 profile31_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,65] 6 51 profile31_node29_cert).mp (by decide +kernel))

def profile31_node30_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 70 57 49 49 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 70 72 64 96 64) }] }

theorem profile31_node30 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,66] 6 49 profile31_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,66] 6 49 profile31_node30_cert).mp (by decide +kernel))

def profile31_node31_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 81 35 84 43 51 35 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile31_node31 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,80] 6 35 profile31_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,80] 6 35 profile31_node31_cert).mp (by decide +kernel))

def profile31_node32_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 100 27 19 51 64), lower := (rows 81 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 102 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 103 100 72 64 100 64) }] }

theorem profile31_node32 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,96] 6 19 profile31_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33,96] 6 19 profile31_node32_cert).mp (by decide +kernel))

def profile31_node22_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node22_route : Route 7 := (fun mask => (mask,id))

theorem profile31_node22 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile31_node22_route profile31_node22_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node23
  · exact profile31_node24
  · exact profile31_node25
  · exact profile31_node26
  · exact profile31_node27
  · exact profile31_node28
  · exact profile31_node29
  · exact profile31_node30
  · exact profile31_node31
  · exact profile31_node32

def profile31_node34_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 81 50 7 105 113 97 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 105 98 111 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile31_node34 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,3] 6 97 profile31_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,3] 6 97 profile31_node34_cert).mp (by decide +kernel))

def profile31_node35_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 50 37 75 83 99 64), lower := (rows 81 50 37 8 16 32 64), losses := [{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 91 69 72 81 64 64) }] }

theorem profile31_node35 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,33] 6 67 profile31_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,33] 6 67 profile31_node35_cert).mp (by decide +kernel))

def profile31_node36_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 81 50 38 73 81 97 64), lower := (rows 81 50 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 102 102 72 64 96 64) }] }

theorem profile31_node36 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,34] 6 65 profile31_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,34] 6 65 profile31_node36_cert).mp (by decide +kernel))

def profile31_node37_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 50 69 43 51 35 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 98 69 72 64 96 64) },{ target := 5, region := (rows 19 2 23 8 16 0 127), good := (rows 85 87 69 72 85 64 64) }] }

theorem profile31_node37 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,65] 6 35 profile31_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,65] 6 35 profile31_node37_cert).mp (by decide +kernel))

def profile31_node38_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 81 50 70 41 49 33 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 102 70 72 64 96 64) }] }

theorem profile31_node38 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,66] 6 33 profile31_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,66] 6 33 profile31_node38_cert).mp (by decide +kernel))

def profile31_node39_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 50 100 11 19 35 64), lower := (rows 81 50 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 118 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 102 100 72 64 100 64) }] }

theorem profile31_node39 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,96] 6 3 profile31_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48,96] 6 3 profile31_node39_cert).mp (by decide +kernel))

def profile31_node33_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile31_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile31_node33 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,48] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile31_node33_route profile31_node33_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node34
  · exact profile31_node35
  · exact profile31_node36
  · exact profile31_node37
  · exact profile31_node38
  · exact profile31_node39

def profile31_node40_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 81 67 55 59 51 51 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile31_node40 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,65] 6 51 profile31_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,65] 6 51 profile31_node40_cert).mp (by decide +kernel))

def profile31_node41_cert : CutBound 7 := { lost := (rows 32 33 0 0 0 0 0), upper := (rows 81 82 39 43 51 35 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile31_node41 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,80] 6 35 profile31_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,80] 6 35 profile31_node41_cert).mp (by decide +kernel))

def profile31_node42_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 81 98 55 59 51 51 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 65 98 68 72 64 98 64) }] }

theorem profile31_node42 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,96] 6 51 profile31_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80,96] 6 51 profile31_node42_cert).mp (by decide +kernel))

def profile31_node20_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile31_node20 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile31_node20_route profile31_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile31_node21
  · exact profile31_node22
  · exact profile31_node33
  · exact profile31_node40
  · exact profile31_node41
  · exact profile31_node42

def profile31_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile31_node0_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile31_node0 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [] 6 (by decide) (choices 2) [18,48,66,80] profile31_node0_route profile31_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node1
  · exact profile31_node14
  · exact profile31_node19
  · exact profile31_node20

theorem profile31 : Upper (D (n:=7) [35,33,32,32,18,18,2]) (R (n:=7) [35,33,32,32,18,18,2]) [] 6 := profile31_node0


#print axioms profile31
end Delivery.SmallBudgetTenFinite7
