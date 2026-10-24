import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile6_node2_cert : CutBound 7 := { lost := (rows 0 64 0 0 0 0 0), upper := (rows 23 35 103 107 115 32 64), lower := (rows 23 35 4 8 16 32 64), losses := [{ target := 6, region := (rows 1 3 4 8 16 127 0), good := (rows 55 35 36 40 48 32 32) }] }

theorem profile6_node2 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,33] 6 99 profile6_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,33] 6 99 profile6_node2_cert).mp (by decide +kernel))

def profile6_node3_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 23 98 103 107 115 32 64), lower := (rows 23 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 118 98 102 106 114 98 98) }] }

theorem profile6_node3 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,96] 6 99 profile6_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22,96] 6 99 profile6_node3_cert).mp (by decide +kernel))

def profile6_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node1 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [22] 6 (by decide) (choices 2) [33,96] profile6_node1_route profile6_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node2
  · exact profile6_node3

def profile6_node6_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 39 19 7 104 112 32 64), lower := (rows 39 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 126 120 120 120 120) }] }

theorem profile6_node6 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,3] 6 96 profile6_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,3] 6 96 profile6_node6_cert).mp (by decide +kernel))

def profile6_node7_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 39 19 37 74 82 32 64), lower := (rows 39 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) }] }

theorem profile6_node7 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,33] 6 66 profile6_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,33] 6 66 profile6_node7_cert).mp (by decide +kernel))

def profile6_node8_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 39 19 38 73 81 32 64), lower := (rows 39 19 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 118 102 104 112 96 96) }] }

theorem profile6_node8 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,34] 6 65 profile6_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,34] 6 65 profile6_node8_cert).mp (by decide +kernel))

def profile6_node9_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 39 19 69 106 114 32 64), lower := (rows 39 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) }] }

theorem profile6_node9 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,65] 6 98 profile6_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,65] 6 98 profile6_node9_cert).mp (by decide +kernel))

def profile6_node10_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 39 19 70 105 113 32 64), lower := (rows 39 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 118 102 104 112 96 96) }] }

theorem profile6_node10 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,66] 6 97 profile6_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,66] 6 97 profile6_node10_cert).mp (by decide +kernel))

def profile6_node11_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 39 19 100 75 83 32 64), lower := (rows 39 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 118 100 108 116 100 100) }] }

theorem profile6_node11 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,96] 6 67 profile6_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17,96] 6 67 profile6_node11_cert).mp (by decide +kernel))

def profile6_node5_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile6_node5 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,17] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile6_node5_route profile6_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node6
  · exact profile6_node7
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node10
  · exact profile6_node11

def profile6_node12_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 39 35 87 91 83 32 64), lower := (rows 39 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile6_node12 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,33] 6 83 profile6_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,33] 6 83 profile6_node12_cert).mp (by decide +kernel))

def profile6_node13_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 39 50 71 75 83 32 64), lower := (rows 39 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 102 114 100 104 114 96 96) }] }

theorem profile6_node13 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,48] 6 67 profile6_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,48] 6 67 profile6_node13_cert).mp (by decide +kernel))

def profile6_node14_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 39 67 119 123 115 32 64), lower := (rows 39 67 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 71 67 68 72 80 64 64) }] }

theorem profile6_node14 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,65] 6 115 profile6_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,65] 6 115 profile6_node14_cert).mp (by decide +kernel))

def profile6_node15_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 39 82 103 107 115 32 64), lower := (rows 39 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 102 114 100 104 114 96 96) }] }

theorem profile6_node15 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,80] 6 99 profile6_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,80] 6 99 profile6_node15_cert).mp (by decide +kernel))

def profile6_node16_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 39 98 87 91 83 32 64), lower := (rows 39 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) }] }

theorem profile6_node16 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,96] 6 83 profile6_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38,96] 6 83 profile6_node16_cert).mp (by decide +kernel))

def profile6_node4_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile6_node4_route : Route 7 := (fun mask => (mask,id))

theorem profile6_node4 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [38] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile6_node4_route profile6_node4_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node5
  · exact profile6_node12
  · exact profile6_node13
  · exact profile6_node14
  · exact profile6_node15
  · exact profile6_node16

def profile6_node19_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 51 7 7 104 112 32 64), lower := (rows 51 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 126 120 120 120 120) }] }

theorem profile6_node19 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,3] 6 96 profile6_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,3] 6 96 profile6_node19_cert).mp (by decide +kernel))

def profile6_node20_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 51 7 37 74 82 32 64), lower := (rows 51 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) }] }

theorem profile6_node20 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,33] 6 66 profile6_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,33] 6 66 profile6_node20_cert).mp (by decide +kernel))

def profile6_node21_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 51 7 38 73 81 32 64), lower := (rows 51 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 118 102 102 104 112 96 96) }] }

theorem profile6_node21 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,34] 6 65 profile6_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,34] 6 65 profile6_node21_cert).mp (by decide +kernel))

def profile6_node22_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 51 7 69 106 114 32 64), lower := (rows 51 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) }] }

theorem profile6_node22 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,65] 6 98 profile6_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,65] 6 98 profile6_node22_cert).mp (by decide +kernel))

def profile6_node23_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 51 7 70 105 113 32 64), lower := (rows 51 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 118 102 102 104 112 96 96) }] }

theorem profile6_node23 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,66] 6 97 profile6_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,66] 6 97 profile6_node23_cert).mp (by decide +kernel))

def profile6_node24_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 51 7 100 75 83 32 64), lower := (rows 51 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 118 102 100 108 116 100 100) }] }

theorem profile6_node24 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,96] 6 67 profile6_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5,96] 6 67 profile6_node24_cert).mp (by decide +kernel))

def profile6_node18_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile6_node18 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,5] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile6_node18_route profile6_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node19
  · exact profile6_node20
  · exact profile6_node21
  · exact profile6_node22
  · exact profile6_node23
  · exact profile6_node24

def profile6_node25_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 51 35 71 79 87 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile6_node25 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,33] 6 71 profile6_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,33] 6 71 profile6_node25_cert).mp (by decide +kernel))

def profile6_node26_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 38 71 75 83 32 64), lower := (rows 51 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 114 102 102 104 112 96 96) }] }

theorem profile6_node26 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,36] 6 67 profile6_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,36] 6 67 profile6_node26_cert).mp (by decide +kernel))

def profile6_node27_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 51 67 103 111 119 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile6_node27 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,65] 6 103 profile6_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,65] 6 103 profile6_node27_cert).mp (by decide +kernel))

def profile6_node28_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 70 103 107 115 32 64), lower := (rows 51 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 114 102 102 104 112 96 96) }] }

theorem profile6_node28 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,68] 6 99 profile6_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,68] 6 99 profile6_node28_cert).mp (by decide +kernel))

def profile6_node29_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 98 71 79 87 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) }] }

theorem profile6_node29 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,96] 6 71 profile6_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50,96] 6 71 profile6_node29_cert).mp (by decide +kernel))

def profile6_node17_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node17_route : Route 7 := (fun mask => (mask,id))

theorem profile6_node17 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [50] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile6_node17_route profile6_node17_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node18
  · exact profile6_node25
  · exact profile6_node26
  · exact profile6_node27
  · exact profile6_node28
  · exact profile6_node29

def profile6_node31_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 53 35 71 75 83 32 64), lower := (rows 53 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 85 95 68 72 80 64 64) }] }

theorem profile6_node31 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,33] 6 67 profile6_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,33] 6 67 profile6_node31_cert).mp (by decide +kernel))

def profile6_node32_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 53 67 103 107 115 32 64), lower := (rows 53 67 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 87 67 68 72 80 64 64) }] }

theorem profile6_node32 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,65] 6 99 profile6_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,65] 6 99 profile6_node32_cert).mp (by decide +kernel))

def profile6_node33_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 53 98 71 75 83 32 64), lower := (rows 53 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 118 98 102 106 114 98 98) }] }

theorem profile6_node33 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,96] 6 67 profile6_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52,96] 6 67 profile6_node33_cert).mp (by decide +kernel))

def profile6_node30_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node30_route : Route 7 := (fun mask => (mask,id))

theorem profile6_node30 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [52] 6 (by decide) (choices 2) [33,65,96] profile6_node30_route profile6_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node31
  · exact profile6_node32
  · exact profile6_node33

def profile6_node36_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 99 7 7 120 112 32 64), lower := (rows 99 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 126 120 120 120 120) }] }

theorem profile6_node36 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,3] 6 112 profile6_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,3] 6 112 profile6_node36_cert).mp (by decide +kernel))

def profile6_node37_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 99 7 21 106 114 32 64), lower := (rows 99 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) }] }

theorem profile6_node37 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,17] 6 98 profile6_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,17] 6 98 profile6_node37_cert).mp (by decide +kernel))

def profile6_node38_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 99 7 22 105 113 32 64), lower := (rows 99 7 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) }] }

theorem profile6_node38 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,18] 6 97 profile6_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,18] 6 97 profile6_node38_cert).mp (by decide +kernel))

def profile6_node39_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 99 7 37 90 82 32 64), lower := (rows 99 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) }] }

theorem profile6_node39 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,33] 6 82 profile6_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,33] 6 82 profile6_node39_cert).mp (by decide +kernel))

def profile6_node40_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 99 7 38 89 81 32 64), lower := (rows 99 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) }] }

theorem profile6_node40 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,34] 6 81 profile6_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,34] 6 81 profile6_node40_cert).mp (by decide +kernel))

def profile6_node41_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 99 7 52 75 83 32 64), lower := (rows 99 7 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 127 127), good := (rows 98 102 116 104 116 96 96) }] }

theorem profile6_node41 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,48] 6 67 profile6_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,48] 6 67 profile6_node41_cert).mp (by decide +kernel))

def profile6_node42_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 99 7 100 27 19 32 64), lower := (rows 99 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) }] }

theorem profile6_node42 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,96] 6 19 profile6_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5,96] 6 19 profile6_node42_cert).mp (by decide +kernel))

def profile6_node35_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile6_node35_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node35 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,5] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile6_node35_route profile6_node35_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node36
  · exact profile6_node37
  · exact profile6_node38
  · exact profile6_node39
  · exact profile6_node40
  · exact profile6_node41
  · exact profile6_node42

def profile6_node44_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 99 19 7 108 116 32 64), lower := (rows 99 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 127 127), good := (rows 98 114 126 104 112 96 96) }] }

theorem profile6_node44 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,3] 6 100 profile6_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,3] 6 100 profile6_node44_cert).mp (by decide +kernel))

def profile6_node45_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 99 19 37 78 86 32 64), lower := (rows 99 19 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 117 101 104 112 96 96) }] }

theorem profile6_node45 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,33] 6 70 profile6_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,33] 6 70 profile6_node45_cert).mp (by decide +kernel))

def profile6_node46_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 99 19 38 77 85 32 64), lower := (rows 99 19 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 118 102 104 112 96 96) }] }

theorem profile6_node46 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,34] 6 69 profile6_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,34] 6 69 profile6_node46_cert).mp (by decide +kernel))

def profile6_node47_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 99 19 100 15 23 32 64), lower := (rows 99 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 118 100 108 116 100 100) }] }

theorem profile6_node47 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,96] 6 7 profile6_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17,96] 6 7 profile6_node47_cert).mp (by decide +kernel))

def profile6_node43_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node43_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node43 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,17] 6 (by decide) (choices 2) [3,33,34,96] profile6_node43_route profile6_node43_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node44
  · exact profile6_node45
  · exact profile6_node46
  · exact profile6_node47

def profile6_node49_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 99 22 7 105 113 32 64), lower := (rows 99 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 121 124 125 104 112 96 96) }] }

theorem profile6_node49 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,3] 6 97 profile6_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,3] 6 97 profile6_node49_cert).mp (by decide +kernel))

def profile6_node50_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 99 22 37 75 83 32 64), lower := (rows 99 22 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 116 101 104 112 96 96) }] }

theorem profile6_node50 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,33] 6 67 profile6_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,33] 6 67 profile6_node50_cert).mp (by decide +kernel))

def profile6_node51_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 99 22 38 73 81 32 64), lower := (rows 99 22 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 23 8 16 127 127), good := (rows 102 118 102 104 118 96 96) }] }

theorem profile6_node51 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,34] 6 65 profile6_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,34] 6 65 profile6_node51_cert).mp (by decide +kernel))

def profile6_node52_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 99 22 100 11 19 32 64), lower := (rows 99 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 127 8 16 127 127), good := (rows 102 118 100 108 118 100 100) }] }

theorem profile6_node52 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,96] 6 3 profile6_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20,96] 6 3 profile6_node52_cert).mp (by decide +kernel))

def profile6_node48_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile6_node48_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node48 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,20] 6 (by decide) (choices 2) [3,33,34,96] profile6_node48_route profile6_node48_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node49
  · exact profile6_node50
  · exact profile6_node51
  · exact profile6_node52

def profile6_node53_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 99 35 87 95 87 32 64), lower := (rows 99 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile6_node53 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,33] 6 87 profile6_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,33] 6 87 profile6_node53_cert).mp (by decide +kernel))

def profile6_node54_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 99 38 87 91 83 32 64), lower := (rows 99 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) }] }

theorem profile6_node54 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,36] 6 83 profile6_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,36] 6 83 profile6_node54_cert).mp (by decide +kernel))

def profile6_node55_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 99 50 71 79 87 32 64), lower := (rows 99 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 98 114 100 104 114 96 96) }] }

theorem profile6_node55 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,48] 6 71 profile6_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,48] 6 71 profile6_node55_cert).mp (by decide +kernel))

def profile6_node56_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 99 98 23 31 23 32 64), lower := (rows 99 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) }] }

theorem profile6_node56 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,96] 6 23 profile6_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98,96] 6 23 profile6_node56_cert).mp (by decide +kernel))

def profile6_node34_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile6_node34_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node34 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [98] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile6_node34_route profile6_node34_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node35
  · exact profile6_node43
  · exact profile6_node48
  · exact profile6_node53
  · exact profile6_node54
  · exact profile6_node55
  · exact profile6_node56

def profile6_node57_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 101 115 119 123 115 32 64), lower := (rows 101 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 101 104 112 96 96) }] }

theorem profile6_node57 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [100] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [100] 6 115 profile6_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [100] 6 115 profile6_node57_cert).mp (by decide +kernel))

def profile6_node58_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 113 103 103 111 119 32 64), lower := (rows 113 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 96 100 104 113 96 96) }] }

theorem profile6_node58 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [112] 6 103 profile6_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [112] 6 103 profile6_node58_cert).mp (by decide +kernel))

def profile6_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile6_node0_route : Route 7 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node0 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [] 6 (by decide) (choices 3) [22,38,50,52,98,100,112] profile6_node0_route profile6_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node1
  · exact profile6_node4
  · exact profile6_node17
  · exact profile6_node30
  · exact profile6_node34
  · exact profile6_node57
  · exact profile6_node58

theorem profile6 : Upper (D (n:=7) [50,34,33,32,17,2,2]) (R (n:=7) [50,34,33,32,17,2,2]) [] 6 := profile6_node0


#print axioms profile6
end Delivery.SmallBudgetTenFinite7
