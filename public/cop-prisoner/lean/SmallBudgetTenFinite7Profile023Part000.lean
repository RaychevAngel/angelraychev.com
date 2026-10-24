import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile23_node2_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 7 7 119 123 115 115 64), lower := (rows 7 7 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 11 19 35 127), good := (rows 123 123 64 72 80 96 64) }] }

theorem profile23_node2 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,5] 6 115 profile23_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,5] 6 115 profile23_node2_cert).mp (by decide +kernel))

def profile23_node4_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 7 108 116 100 64), lower := (rows 7 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 13 21 37 127), good := (rows 126 122 126 72 80 96 64) }] }

theorem profile23_node4 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,3] 6 100 profile23_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,3] 6 100 profile23_node4_cert).mp (by decide +kernel))

def profile23_node5_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 37 78 86 102 64), lower := (rows 7 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 9 17 33 127), good := (rows 126 122 124 72 80 96 64) }] }

theorem profile23_node5 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,33] 6 70 profile23_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,33] 6 70 profile23_node5_cert).mp (by decide +kernel))

def profile23_node6_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 7 19 38 77 85 101 64), lower := (rows 7 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 125 121 100 72 80 96 64) }] }

theorem profile23_node6 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,34] 6 69 profile23_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,34] 6 69 profile23_node6_cert).mp (by decide +kernel))

def profile23_node7_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 69 110 118 102 64), lower := (rows 7 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 9 17 33 127), good := (rows 126 122 124 72 80 96 64) }] }

theorem profile23_node7 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,65] 6 102 profile23_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,65] 6 102 profile23_node7_cert).mp (by decide +kernel))

def profile23_node8_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 70 109 117 101 64), lower := (rows 7 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 86 70 72 80 96 64) }] }

theorem profile23_node8 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,66] 6 101 profile23_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,66] 6 101 profile23_node8_cert).mp (by decide +kernel))

def profile23_node9_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 100 79 87 103 64), lower := (rows 7 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 70 82 100 72 80 100 64) }] }

theorem profile23_node9 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,96] 6 71 profile23_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17,96] 6 71 profile23_node9_cert).mp (by decide +kernel))

def profile23_node3_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile23_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node3 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,17] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile23_node3_route profile23_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node4
  · exact profile23_node5
  · exact profile23_node6
  · exact profile23_node7
  · exact profile23_node8
  · exact profile23_node9

def profile23_node10_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 7 22 103 107 115 99 64), lower := (rows 7 22 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 17 33 127), good := (rows 123 82 64 72 80 96 64) }] }

theorem profile23_node10 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,20] 6 99 profile23_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,20] 6 99 profile23_node10_cert).mp (by decide +kernel))

def profile23_node12_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 7 50 7 77 85 101 64), lower := (rows 7 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 125 112 125 72 80 96 64) }] }

theorem profile23_node12 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,3] 6 69 profile23_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,3] 6 69 profile23_node12_cert).mp (by decide +kernel))

def profile23_node13_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 7 50 69 79 87 103 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 112 69 72 80 96 64) }] }

theorem profile23_node13 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,65] 6 71 profile23_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,65] 6 71 profile23_node13_cert).mp (by decide +kernel))

def profile23_node14_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 50 70 77 85 101 64), lower := (rows 7 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 118 70 72 80 96 64) }] }

theorem profile23_node14 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,66] 6 69 profile23_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48,66] 6 69 profile23_node14_cert).mp (by decide +kernel))

def profile23_node11_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile23_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node11 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,48] 6 (by decide) (choices 2) [3,65,66] profile23_node11_route profile23_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node12
  · exact profile23_node13
  · exact profile23_node14

def profile23_node15_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 7 67 119 127 119 119 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 16 32 127), good := (rows 67 67 64 72 80 96 64) }] }

theorem profile23_node15 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,65] 6 119 profile23_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,65] 6 119 profile23_node15_cert).mp (by decide +kernel))

def profile23_node16_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 70 119 123 115 115 64), lower := (rows 7 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 7 4 8 16 32 127), good := (rows 70 70 70 72 80 96 64) }] }

theorem profile23_node16 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,68] 6 115 profile23_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,68] 6 115 profile23_node16_cert).mp (by decide +kernel))

def profile23_node17_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 82 103 111 119 103 64), lower := (rows 7 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 68 72 82 96 64) }] }

theorem profile23_node17 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,80] 6 103 profile23_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6,80] 6 103 profile23_node17_cert).mp (by decide +kernel))

def profile23_node1_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile23_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile23_node1 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [6] 6 (by decide) (choices 2) [5,17,20,48,65,68,80] profile23_node1_route profile23_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node2
  · exact profile23_node3
  · exact profile23_node10
  · exact profile23_node11
  · exact profile23_node15
  · exact profile23_node16
  · exact profile23_node17

def profile23_node20_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 7 108 116 100 64), lower := (rows 19 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 122 126 126 72 80 96 64) }] }

theorem profile23_node20 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,3] 6 100 profile23_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,3] 6 100 profile23_node20_cert).mp (by decide +kernel))

def profile23_node21_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 37 78 86 102 64), lower := (rows 19 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 122 126 100 72 80 96 64) }] }

theorem profile23_node21 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,33] 6 70 profile23_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,33] 6 70 profile23_node21_cert).mp (by decide +kernel))

def profile23_node22_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 19 7 38 77 85 101 64), lower := (rows 19 7 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 10 18 34 127), good := (rows 121 125 124 72 80 96 64) }] }

theorem profile23_node22 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,34] 6 69 profile23_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,34] 6 69 profile23_node22_cert).mp (by decide +kernel))

def profile23_node23_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 69 110 118 102 64), lower := (rows 19 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 122 126 68 72 80 96 64) }] }

theorem profile23_node23 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,65] 6 102 profile23_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,65] 6 102 profile23_node23_cert).mp (by decide +kernel))

def profile23_node24_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 70 109 117 101 64), lower := (rows 19 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 70 70 72 80 96 64) }] }

theorem profile23_node24 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,66] 6 101 profile23_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,66] 6 101 profile23_node24_cert).mp (by decide +kernel))

def profile23_node25_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 100 79 87 103 64), lower := (rows 19 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 70 100 72 80 100 64) }] }

theorem profile23_node25 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,96] 6 71 profile23_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5,96] 6 71 profile23_node25_cert).mp (by decide +kernel))

def profile23_node19_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile23_node19_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node19 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,5] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile23_node19_route profile23_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node20
  · exact profile23_node21
  · exact profile23_node22
  · exact profile23_node23
  · exact profile23_node24
  · exact profile23_node25

def profile23_node27_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 35 7 76 84 100 64), lower := (rows 19 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 126 72 80 96 64) }] }

theorem profile23_node27 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,3] 6 68 profile23_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,3] 6 68 profile23_node27_cert).mp (by decide +kernel))

def profile23_node28_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 19 35 69 78 86 102 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 101 69 72 80 96 64) }] }

theorem profile23_node28 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,65] 6 70 profile23_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,65] 6 70 profile23_node28_cert).mp (by decide +kernel))

def profile23_node29_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 70 77 85 101 64), lower := (rows 19 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 102 70 72 80 96 64) }] }

theorem profile23_node29 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,66] 6 69 profile23_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33,66] 6 69 profile23_node29_cert).mp (by decide +kernel))

def profile23_node26_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile23_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node26 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,33] 6 (by decide) (choices 2) [3,65,66] profile23_node26_route profile23_node26_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node27
  · exact profile23_node28
  · exact profile23_node29

def profile23_node31_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 19 38 7 77 85 101 64), lower := (rows 19 38 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 81 124 125 72 80 96 64) }] }

theorem profile23_node31 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,3] 6 69 profile23_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,3] 6 69 profile23_node31_cert).mp (by decide +kernel))

def profile23_node32_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 19 38 69 79 87 103 64), lower := (rows 19 38 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 100 69 72 80 96 64) }] }

theorem profile23_node32 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,65] 6 71 profile23_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,65] 6 71 profile23_node32_cert).mp (by decide +kernel))

def profile23_node33_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 19 38 70 77 85 101 64), lower := (rows 19 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 39 8 16 32 127), good := (rows 86 102 70 72 80 102 64) }] }

theorem profile23_node33 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,66] 6 69 profile23_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36,66] 6 69 profile23_node33_cert).mp (by decide +kernel))

def profile23_node30_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile23_node30_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node30 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,36] 6 (by decide) (choices 2) [3,65,66] profile23_node30_route profile23_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node31
  · exact profile23_node32
  · exact profile23_node33

def profile23_node34_cert : CutBound 7 := { lost := (rows 4 4 0 0 0 0 0), upper := (rows 19 67 103 111 119 103 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 2, region := (rows 17 19 0 8 16 32 127), good := (rows 83 67 64 72 83 96 64) }] }

theorem profile23_node34 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,65] 6 103 profile23_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,65] 6 103 profile23_node34_cert).mp (by decide +kernel))

def profile23_node35_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 70 103 111 119 103 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 70 70 72 80 96 64) }] }

theorem profile23_node35 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,68] 6 103 profile23_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,68] 6 103 profile23_node35_cert).mp (by decide +kernel))

def profile23_node36_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 98 71 79 87 103 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) }] }

theorem profile23_node36 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,96] 6 71 profile23_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18,96] 6 71 profile23_node36_cert).mp (by decide +kernel))

def profile23_node18_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile23_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node18 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [18] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile23_node18_route profile23_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node19
  · exact profile23_node26
  · exact profile23_node30
  · exact profile23_node34
  · exact profile23_node35
  · exact profile23_node36

def profile23_node39_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 7 78 86 102 64), lower := (rows 49 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 112 126 126 72 80 96 64) }] }

theorem profile23_node39 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,3] 6 70 profile23_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,3] 6 70 profile23_node39_cert).mp (by decide +kernel))

def profile23_node40_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 69 78 86 102 64), lower := (rows 49 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 68 72 80 96 64) }] }

theorem profile23_node40 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,65] 6 70 profile23_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,65] 6 70 profile23_node40_cert).mp (by decide +kernel))

def profile23_node41_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 7 70 79 87 103 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) }] }

theorem profile23_node41 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,66] 6 71 profile23_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5,66] 6 71 profile23_node41_cert).mp (by decide +kernel))

def profile23_node38_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile23_node38_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node38 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,5] 6 (by decide) (choices 2) [3,65,66] profile23_node38_route profile23_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node39
  · exact profile23_node40
  · exact profile23_node41

def profile23_node42_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 49 67 71 79 87 103 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 16 32 127), good := (rows 115 67 64 72 80 96 64) }] }

theorem profile23_node42 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,65] 6 71 profile23_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,65] 6 71 profile23_node42_cert).mp (by decide +kernel))

def profile23_node43_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 70 71 79 87 103 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 112 70 70 72 80 96 64) }] }

theorem profile23_node43 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,68] 6 71 profile23_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48,68] 6 71 profile23_node43_cert).mp (by decide +kernel))

def profile23_node37_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 12 => 3 | 20 => 4 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile23_node37_route : Route 7 := (fun mask => (mask,id))

theorem profile23_node37 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [48] 6 (by decide) (choices 2) [5,65,68] profile23_node37_route profile23_node37_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node38
  · exact profile23_node42
  · exact profile23_node43

def profile23_node44_cert : CutBound 7 := { lost := (rows 4 0 0 0 0 0 0), upper := (rows 67 119 119 127 119 119 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 2, region := (rows 3 2 0 8 16 32 127), good := (rows 67 67 64 72 80 96 64) }] }

theorem profile23_node44 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [66] 6 119 profile23_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [66] 6 119 profile23_node44_cert).mp (by decide +kernel))

def profile23_node45_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 81 103 103 111 119 103 64), lower := (rows 81 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 64 68 72 81 96 64) }] }

theorem profile23_node45 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [80] 6 103 profile23_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [80] 6 103 profile23_node45_cert).mp (by decide +kernel))

def profile23_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile23_node0_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile23_node0 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [] 6 (by decide) (choices 2) [6,18,48,66,80] profile23_node0_route profile23_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile23_node1
  · exact profile23_node18
  · exact profile23_node37
  · exact profile23_node44
  · exact profile23_node45

theorem profile23 : Upper (D (n:=7) [34,34,34,32,17,17,2]) (R (n:=7) [34,34,34,32,17,17,2]) [] 6 := profile23_node0


#print axioms profile23
end Delivery.SmallBudgetTenFinite7
