import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile7_node2_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 7 102 106 114 32 64), lower := (rows 23 7 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 11 19 127 127), good := (rows 123 123 96 104 112 96 96) }] }

theorem profile7_node2 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,5] 6 98 profile7_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,5] 6 98 profile7_node2_cert).mp (by decide +kernel))

def profile7_node3_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 23 35 102 110 118 32 64), lower := (rows 23 35 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 115 99 96 104 112 96 96) }] }

theorem profile7_node3 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,33] 6 102 profile7_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,33] 6 102 profile7_node3_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 38 103 107 115 32 64), lower := (rows 23 38 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 17 127 127), good := (rows 123 98 96 104 112 96 96) }] }

theorem profile7_node4 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,36] 6 99 profile7_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,36] 6 99 profile7_node4_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 23 98 103 111 119 32 64), lower := (rows 23 98 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 115 98 98 106 114 98 98) }] }

theorem profile7_node5 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,96] 6 103 profile7_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22,96] 6 103 profile7_node5_cert).mp (by decide +kernel))

def profile7_node1_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile7_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile7_node1 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [22] 6 (by decide) (choices 2) [5,33,36,96] profile7_node1_route profile7_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node4
  · exact profile7_node5

def profile7_node7_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 39 7 118 122 114 32 64), lower := (rows 39 7 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 11 19 127 127), good := (rows 123 123 96 104 112 96 96) }] }

theorem profile7_node7 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,5] 6 114 profile7_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,5] 6 114 profile7_node7_cert).mp (by decide +kernel))

def profile7_node9_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 39 19 38 76 84 32 64), lower := (rows 39 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 121 124 104 112 96 96) }] }

theorem profile7_node9 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,34] 6 68 profile7_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,34] 6 68 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 39 19 70 108 116 32 64), lower := (rows 39 19 70 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 121 124 104 112 96 96) }] }

theorem profile7_node10 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,66] 6 100 profile7_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,66] 6 100 profile7_node10_cert).mp (by decide +kernel))

def profile7_node11_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 39 19 100 78 86 32 64), lower := (rows 39 19 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 117 100 108 116 100 100) }] }

theorem profile7_node11 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,96] 6 70 profile7_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17,96] 6 70 profile7_node11_cert).mp (by decide +kernel))

def profile7_node8_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile7_node8_route : Route 7 := (fun mask => (mask,id))

theorem profile7_node8 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,17] 6 (by decide) (choices 2) [34,66,96] profile7_node8_route profile7_node8_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node9
  · exact profile7_node10
  · exact profile7_node11

def profile7_node12_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 39 22 103 107 115 32 64), lower := (rows 39 22 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 17 127 127), good := (rows 123 114 96 104 112 96 96) }] }

theorem profile7_node12 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,20] 6 99 profile7_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,20] 6 99 profile7_node12_cert).mp (by decide +kernel))

def profile7_node13_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 39 35 86 94 86 32 64), lower := (rows 39 35 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) }] }

theorem profile7_node13 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,33] 6 86 profile7_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,33] 6 86 profile7_node13_cert).mp (by decide +kernel))

def profile7_node14_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 39 38 87 91 83 32 64), lower := (rows 39 38 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 17 127 127), good := (rows 123 98 96 104 112 96 96) }] }

theorem profile7_node14 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,36] 6 83 profile7_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,36] 6 83 profile7_node14_cert).mp (by decide +kernel))

def profile7_node15_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 39 50 71 79 87 32 64), lower := (rows 39 50 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 18 0 8 16 127 127), good := (rows 99 114 96 104 114 96 96) }] }

theorem profile7_node15 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,48] 6 71 profile7_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,48] 6 71 profile7_node15_cert).mp (by decide +kernel))

def profile7_node16_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 39 67 118 126 118 32 64), lower := (rows 39 67 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) }] }

theorem profile7_node16 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,65] 6 118 profile7_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,65] 6 118 profile7_node16_cert).mp (by decide +kernel))

def profile7_node17_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 39 70 119 123 115 32 64), lower := (rows 39 70 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 17 127 127), good := (rows 123 98 96 104 112 96 96) }] }

theorem profile7_node17 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,68] 6 115 profile7_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,68] 6 115 profile7_node17_cert).mp (by decide +kernel))

def profile7_node18_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 39 82 103 111 119 32 64), lower := (rows 39 82 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 18 0 8 16 127 127), good := (rows 99 114 96 104 114 96 96) }] }

theorem profile7_node18 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,80] 6 103 profile7_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,80] 6 103 profile7_node18_cert).mp (by decide +kernel))

def profile7_node19_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 39 98 87 95 87 32 64), lower := (rows 39 98 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 99 98 98 106 114 98 98) }] }

theorem profile7_node19 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,96] 6 87 profile7_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38,96] 6 87 profile7_node19_cert).mp (by decide +kernel))

def profile7_node6_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile7_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile7_node6 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [38] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile7_node6_route profile7_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node7
  · exact profile7_node8
  · exact profile7_node12
  · exact profile7_node13
  · exact profile7_node14
  · exact profile7_node15
  · exact profile7_node16
  · exact profile7_node17
  · exact profile7_node18
  · exact profile7_node19

def profile7_node22_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 51 7 38 76 84 32 64), lower := (rows 51 7 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 14 22 127 127), good := (rows 121 125 124 104 112 96 96) }] }

theorem profile7_node22 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,34] 6 68 profile7_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,34] 6 68 profile7_node22_cert).mp (by decide +kernel))

def profile7_node23_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 51 7 70 108 116 32 64), lower := (rows 51 7 70 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 14 22 127 127), good := (rows 121 125 124 104 112 96 96) }] }

theorem profile7_node23 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,66] 6 100 profile7_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,66] 6 100 profile7_node23_cert).mp (by decide +kernel))

def profile7_node24_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 51 7 100 78 86 32 64), lower := (rows 51 7 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 117 101 100 108 116 100 100) }] }

theorem profile7_node24 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,96] 6 70 profile7_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5,96] 6 70 profile7_node24_cert).mp (by decide +kernel))

def profile7_node21_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile7_node21_route : Route 7 := (fun mask => (mask,id))

theorem profile7_node21 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,5] 6 (by decide) (choices 2) [34,66,96] profile7_node21_route profile7_node21_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node22
  · exact profile7_node23
  · exact profile7_node24

def profile7_node25_cert : CutBound 7 := { lost := (rows 4 4 0 0 0 0 0), upper := (rows 51 35 70 78 86 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 2, region := (rows 17 19 0 8 16 127 127), good := (rows 115 99 96 104 115 96 96) }] }

theorem profile7_node25 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,33] 6 70 profile7_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,33] 6 70 profile7_node25_cert).mp (by decide +kernel))

def profile7_node26_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 51 38 71 79 87 32 64), lower := (rows 51 38 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) }] }

theorem profile7_node26 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,36] 6 71 profile7_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,36] 6 71 profile7_node26_cert).mp (by decide +kernel))

def profile7_node27_cert : CutBound 7 := { lost := (rows 4 4 0 0 0 0 0), upper := (rows 51 67 102 110 118 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 2, region := (rows 17 19 0 8 16 127 127), good := (rows 115 99 96 104 115 96 96) }] }

theorem profile7_node27 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,65] 6 102 profile7_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,65] 6 102 profile7_node27_cert).mp (by decide +kernel))

def profile7_node28_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 51 70 103 111 119 32 64), lower := (rows 51 70 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 83 70 70 72 80 64 64) }] }

theorem profile7_node28 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,68] 6 103 profile7_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,68] 6 103 profile7_node28_cert).mp (by decide +kernel))

def profile7_node29_cert : CutBound 7 := { lost := (rows 4 4 0 0 0 0 0), upper := (rows 51 98 71 79 87 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 2, region := (rows 17 127 0 8 16 127 127), good := (rows 115 98 98 106 115 98 98) }] }

theorem profile7_node29 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,96] 6 71 profile7_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50,96] 6 71 profile7_node29_cert).mp (by decide +kernel))

def profile7_node20_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile7_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile7_node20 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [50] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile7_node20_route profile7_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node21
  · exact profile7_node25
  · exact profile7_node26
  · exact profile7_node27
  · exact profile7_node28
  · exact profile7_node29

def profile7_node30_cert : CutBound 7 := { lost := (rows 4 0 0 0 0 0 0), upper := (rows 99 119 119 127 119 32 64), lower := (rows 99 2 4 8 16 32 64), losses := [{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) }] }

theorem profile7_node30 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [98] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [98] 6 119 profile7_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [98] 6 119 profile7_node30_cert).mp (by decide +kernel))

def profile7_node31_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 113 103 103 111 119 32 64), lower := (rows 113 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 96 100 104 113 96 96) }] }

theorem profile7_node31 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [112] 6 103 profile7_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [112] 6 103 profile7_node31_cert).mp (by decide +kernel))

def profile7_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile7_node0_route : Route 7 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 100 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile7_node0 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [] 6 (by decide) (choices 3) [22,38,50,98,112] profile7_node0_route profile7_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile7_node1
  · exact profile7_node6
  · exact profile7_node20
  · exact profile7_node30
  · exact profile7_node31

theorem profile7 : Upper (D (n:=7) [49,34,34,32,17,2,2]) (R (n:=7) [49,34,34,32,17,2,2]) [] 6 := profile7_node0


#print axioms profile7
end Delivery.SmallBudgetTenFinite7
