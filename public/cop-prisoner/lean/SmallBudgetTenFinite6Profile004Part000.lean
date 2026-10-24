import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile4_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 15 7 54 58 50 32), lower := (rows 15 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) }] }

theorem profile4_node2 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,5] 6 50 profile4_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,5] 6 50 profile4_node2_cert).mp (by decide +kernel))

def profile4_node4_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 15 19 22 44 52 32), lower := (rows 15 19 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node4 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,18] 6 36 profile4_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,18] 6 36 profile4_node4_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 15 19 38 60 52 32), lower := (rows 15 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node5 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,34] 6 52 profile4_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,34] 6 52 profile4_node5_cert).mp (by decide +kernel))

def profile4_node6_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 15 19 52 46 54 32), lower := (rows 15 19 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 45 53 52 40 52 32) }] }

theorem profile4_node6 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,48] 6 38 profile4_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17,48] 6 38 profile4_node6_cert).mp (by decide +kernel))

def profile4_node3_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,17] 6 (by decide) (choices 2) [18,34,48] profile4_node3_route profile4_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node4
  · exact profile4_node5
  · exact profile4_node6

def profile4_node7_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 15 22 55 59 51 32), lower := (rows 15 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 50 32 40 48 32) }] }

theorem profile4_node7 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,20] 6 51 profile4_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,20] 6 51 profile4_node7_cert).mp (by decide +kernel))

def profile4_node8_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 15 35 54 62 54 32), lower := (rows 15 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 43 35 32 40 48 32) }] }

theorem profile4_node8 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,33] 6 54 profile4_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,33] 6 54 profile4_node8_cert).mp (by decide +kernel))

def profile4_node9_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 15 38 55 59 51 32), lower := (rows 15 38 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile4_node9 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,36] 6 51 profile4_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,36] 6 51 profile4_node9_cert).mp (by decide +kernel))

def profile4_node10_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 15 50 55 63 55 32), lower := (rows 15 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 43 50 32 40 50 32) }] }

theorem profile4_node10 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,48] 6 55 profile4_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14,48] 6 55 profile4_node10_cert).mp (by decide +kernel))

def profile4_node1_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [14] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile4_node1_route profile4_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node7
  · exact profile4_node8
  · exact profile4_node9
  · exact profile4_node10

def profile4_node12_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 7 62 58 58 32), lower := (rows 23 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) }] }

theorem profile4_node12 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,5] 6 58 profile4_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,5] 6 58 profile4_node12_cert).mp (by decide +kernel))

def profile4_node14_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 23 11 22 44 52 32), lower := (rows 23 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node14 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,18] 6 36 profile4_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,18] 6 36 profile4_node14_cert).mp (by decide +kernel))

def profile4_node15_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 23 11 38 60 52 32), lower := (rows 23 11 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node15 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,34] 6 52 profile4_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,34] 6 52 profile4_node15_cert).mp (by decide +kernel))

def profile4_node16_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 23 11 52 46 54 32), lower := (rows 23 11 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 53 45 52 40 52 32) }] }

theorem profile4_node16 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,48] 6 38 profile4_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9,48] 6 38 profile4_node16_cert).mp (by decide +kernel))

def profile4_node13_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node13 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,9] 6 (by decide) (choices 2) [18,34,48] profile4_node13_route profile4_node13_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node14
  · exact profile4_node15
  · exact profile4_node16

def profile4_node17_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 14 55 59 51 32), lower := (rows 23 14 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 32 40 48 32) }] }

theorem profile4_node17 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,12] 6 51 profile4_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,12] 6 51 profile4_node17_cert).mp (by decide +kernel))

def profile4_node18_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 23 19 46 46 62 32), lower := (rows 23 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 51 51 32 40 48 32) }] }

theorem profile4_node18 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,17] 6 46 profile4_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,17] 6 46 profile4_node18_cert).mp (by decide +kernel))

def profile4_node19_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 22 47 43 59 32), lower := (rows 23 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 50 32 40 48 32) }] }

theorem profile4_node19 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,20] 6 43 profile4_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,20] 6 43 profile4_node19_cert).mp (by decide +kernel))

def profile4_node20_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 23 26 39 47 55 32), lower := (rows 23 26 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 63), good := (rows 47 42 36 40 32 32) }] }

theorem profile4_node20 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,24] 6 39 profile4_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,24] 6 39 profile4_node20_cert).mp (by decide +kernel))

def profile4_node21_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 23 35 62 62 62 32), lower := (rows 23 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 51 35 32 40 48 32) }] }

theorem profile4_node21 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,33] 6 62 profile4_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,33] 6 62 profile4_node21_cert).mp (by decide +kernel))

def profile4_node22_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 23 38 63 59 59 32), lower := (rows 23 38 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile4_node22 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,36] 6 59 profile4_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,36] 6 59 profile4_node22_cert).mp (by decide +kernel))

def profile4_node23_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 23 42 55 63 55 32), lower := (rows 23 42 4 8 16 32), losses := [{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 51 42 32 42 48 32) }] }

theorem profile4_node23 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,40] 6 55 profile4_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,40] 6 55 profile4_node23_cert).mp (by decide +kernel))

def profile4_node24_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 23 50 47 47 63 32), lower := (rows 23 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 19 0 8 16 63), good := (rows 51 50 32 40 50 32) }] }

theorem profile4_node24 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,48] 6 47 profile4_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22,48] 6 47 profile4_node24_cert).mp (by decide +kernel))

def profile4_node11_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile4_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node11 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [22] 6 (by decide) (choices 2) [5,9,12,17,20,24,33,36,40,48] profile4_node11_route profile4_node11_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node12
  · exact profile4_node13
  · exact profile4_node17
  · exact profile4_node18
  · exact profile4_node19
  · exact profile4_node20
  · exact profile4_node21
  · exact profile4_node22
  · exact profile4_node23
  · exact profile4_node24

def profile4_node27_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 27 7 22 44 52 32), lower := (rows 27 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node27 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,18] 6 36 profile4_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,18] 6 36 profile4_node27_cert).mp (by decide +kernel))

def profile4_node28_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 27 7 38 60 52 32), lower := (rows 27 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node28 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,34] 6 52 profile4_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,34] 6 52 profile4_node28_cert).mp (by decide +kernel))

def profile4_node29_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 27 7 52 46 54 32), lower := (rows 27 7 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 61 37 52 40 52 32) }] }

theorem profile4_node29 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,48] 6 38 profile4_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5,48] 6 38 profile4_node29_cert).mp (by decide +kernel))

def profile4_node26_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node26_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node26 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,5] 6 (by decide) (choices 2) [18,34,48] profile4_node26_route profile4_node26_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node27
  · exact profile4_node28
  · exact profile4_node29

def profile4_node30_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 27 19 38 46 54 32), lower := (rows 27 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 59 51 32 40 48 32) }] }

theorem profile4_node30 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,17] 6 38 profile4_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,17] 6 38 profile4_node30_cert).mp (by decide +kernel))

def profile4_node31_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 27 22 39 47 55 32), lower := (rows 27 22 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 63), good := (rows 47 38 36 40 32 32) }] }

theorem profile4_node31 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,20] 6 39 profile4_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,20] 6 39 profile4_node31_cert).mp (by decide +kernel))

def profile4_node32_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 27 35 54 62 54 32), lower := (rows 27 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 59 35 32 40 48 32) }] }

theorem profile4_node32 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,33] 6 54 profile4_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,33] 6 54 profile4_node32_cert).mp (by decide +kernel))

def profile4_node33_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 27 38 55 63 55 32), lower := (rows 27 38 4 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 63), good := (rows 43 38 38 40 32 32) }] }

theorem profile4_node33 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,36] 6 55 profile4_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,36] 6 55 profile4_node33_cert).mp (by decide +kernel))

def profile4_node34_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 27 50 39 47 55 32), lower := (rows 27 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 19 0 8 16 63), good := (rows 59 50 32 40 50 32) }] }

theorem profile4_node34 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,48] 6 39 profile4_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26,48] 6 39 profile4_node34_cert).mp (by decide +kernel))

def profile4_node25_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node25 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [26] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile4_node25_route profile4_node25_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node26
  · exact profile4_node30
  · exact profile4_node31
  · exact profile4_node32
  · exact profile4_node33
  · exact profile4_node34

def profile4_node36_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 39 7 62 58 58 32), lower := (rows 39 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) }] }

theorem profile4_node36 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,5] 6 58 profile4_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,5] 6 58 profile4_node36_cert).mp (by decide +kernel))

def profile4_node38_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 11 22 60 52 32), lower := (rows 39 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node38 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,18] 6 52 profile4_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,18] 6 52 profile4_node38_cert).mp (by decide +kernel))

def profile4_node39_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 11 38 28 20 32), lower := (rows 39 11 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node39 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,34] 6 20 profile4_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,34] 6 20 profile4_node39_cert).mp (by decide +kernel))

def profile4_node40_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 11 52 30 22 32), lower := (rows 39 11 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 37 41 52 40 52 32) }] }

theorem profile4_node40 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,48] 6 22 profile4_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9,48] 6 22 profile4_node40_cert).mp (by decide +kernel))

def profile4_node37_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node37_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node37 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,9] 6 (by decide) (choices 2) [18,34,48] profile4_node37_route profile4_node37_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node38
  · exact profile4_node39
  · exact profile4_node40

def profile4_node41_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 39 14 55 59 51 32), lower := (rows 39 14 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 32 40 48 32) }] }

theorem profile4_node41 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,12] 6 51 profile4_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,12] 6 51 profile4_node41_cert).mp (by decide +kernel))

def profile4_node43_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 19 14 60 52 32), lower := (rows 39 19 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node43 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,10] 6 52 profile4_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,10] 6 52 profile4_node43_cert).mp (by decide +kernel))

def profile4_node44_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 19 22 44 60 32), lower := (rows 39 19 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node44 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,18] 6 44 profile4_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,18] 6 44 profile4_node44_cert).mp (by decide +kernel))

def profile4_node45_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 39 19 28 46 54 32), lower := (rows 39 19 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 63), good := (rows 47 43 44 40 32 32) }] }

theorem profile4_node45 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,24] 6 38 profile4_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,24] 6 38 profile4_node45_cert).mp (by decide +kernel))

def profile4_node46_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 19 38 28 28 32), lower := (rows 39 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile4_node46 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,34] 6 28 profile4_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,34] 6 28 profile4_node46_cert).mp (by decide +kernel))

def profile4_node47_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 19 44 30 22 32), lower := (rows 39 19 44 8 16 32), losses := [{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 37 49 44 44 48 32) }] }

theorem profile4_node47 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,40] 6 22 profile4_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,40] 6 22 profile4_node47_cert).mp (by decide +kernel))

def profile4_node48_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 19 52 14 30 32), lower := (rows 39 19 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 37 53 52 40 52 32) }] }

theorem profile4_node48 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,48] 6 14 profile4_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17,48] 6 14 profile4_node48_cert).mp (by decide +kernel))

def profile4_node42_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | _ => 0

def profile4_node42_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node42 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,17] 6 (by decide) (choices 2) [10,18,24,34,40,48] profile4_node42_route profile4_node42_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node43
  · exact profile4_node44
  · exact profile4_node45
  · exact profile4_node46
  · exact profile4_node47
  · exact profile4_node48

def profile4_node49_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 39 22 63 59 59 32), lower := (rows 39 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 50 32 40 48 32) }] }

theorem profile4_node49 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,20] 6 59 profile4_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,20] 6 59 profile4_node49_cert).mp (by decide +kernel))

def profile4_node51_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 26 7 60 52 32), lower := (rows 39 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 56 61 40 48 32) }] }

theorem profile4_node51 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,3] 6 52 profile4_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,3] 6 52 profile4_node51_cert).mp (by decide +kernel))

def profile4_node52_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 39 26 21 46 54 32), lower := (rows 39 26 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 63), good := (rows 47 42 45 40 32 32) }] }

theorem profile4_node52 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,17] 6 38 profile4_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,17] 6 38 profile4_node52_cert).mp (by decide +kernel))

def profile4_node53_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 26 22 45 53 32), lower := (rows 39 26 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 56 52 40 48 32) }] }

theorem profile4_node53 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,18] 6 37 profile4_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,18] 6 37 profile4_node53_cert).mp (by decide +kernel))

def profile4_node54_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 26 37 30 22 32), lower := (rows 39 26 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 56 37 40 48 32) }] }

theorem profile4_node54 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,33] 6 22 profile4_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,33] 6 22 profile4_node54_cert).mp (by decide +kernel))

def profile4_node55_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 26 38 29 21 32), lower := (rows 39 26 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 56 36 40 48 32) }] }

theorem profile4_node55 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,34] 6 21 profile4_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,34] 6 21 profile4_node55_cert).mp (by decide +kernel))

def profile4_node56_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 26 52 15 23 32), lower := (rows 39 26 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 37 60 52 40 52 32) }] }

theorem profile4_node56 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,48] 6 7 profile4_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24,48] 6 7 profile4_node56_cert).mp (by decide +kernel))

def profile4_node50_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node50 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,24] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile4_node50_route profile4_node50_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node51
  · exact profile4_node52
  · exact profile4_node53
  · exact profile4_node54
  · exact profile4_node55
  · exact profile4_node56

def profile4_node57_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 39 35 30 30 30 32), lower := (rows 39 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 32 40 48 32) }] }

theorem profile4_node57 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,33] 6 30 profile4_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,33] 6 30 profile4_node57_cert).mp (by decide +kernel))

def profile4_node58_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 39 38 31 27 27 32), lower := (rows 39 38 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile4_node58 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,36] 6 27 profile4_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,36] 6 27 profile4_node58_cert).mp (by decide +kernel))

def profile4_node59_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 39 42 23 31 23 32), lower := (rows 39 42 4 8 16 32), losses := [{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 32 42 48 32) }] }

theorem profile4_node59 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,40] 6 23 profile4_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,40] 6 23 profile4_node59_cert).mp (by decide +kernel))

def profile4_node60_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 39 50 31 31 31 32), lower := (rows 39 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 35 50 32 40 50 32) }] }

theorem profile4_node60 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,48] 6 31 profile4_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38,48] 6 31 profile4_node60_cert).mp (by decide +kernel))

def profile4_node35_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile4_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node35 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [38] 6 (by decide) (choices 2) [5,9,12,17,20,24,33,36,40,48] profile4_node35_route profile4_node35_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node36
  · exact profile4_node37
  · exact profile4_node41
  · exact profile4_node42
  · exact profile4_node49
  · exact profile4_node50
  · exact profile4_node57
  · exact profile4_node58
  · exact profile4_node59
  · exact profile4_node60

def profile4_node63_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 43 7 22 60 52 32), lower := (rows 43 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node63 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,18] 6 52 profile4_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,18] 6 52 profile4_node63_cert).mp (by decide +kernel))

def profile4_node64_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 43 7 38 28 20 32), lower := (rows 43 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node64 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,34] 6 20 profile4_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,34] 6 20 profile4_node64_cert).mp (by decide +kernel))

def profile4_node65_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 43 7 52 30 22 32), lower := (rows 43 7 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 41 37 52 40 52 32) }] }

theorem profile4_node65 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,48] 6 22 profile4_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5,48] 6 22 profile4_node65_cert).mp (by decide +kernel))

def profile4_node62_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node62_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node62 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,5] 6 (by decide) (choices 2) [18,34,48] profile4_node62_route profile4_node62_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node63
  · exact profile4_node64
  · exact profile4_node65

def profile4_node67_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 43 19 22 44 52 32), lower := (rows 43 19 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 49 60 40 48 32) }] }

theorem profile4_node67 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,18] 6 36 profile4_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,18] 6 36 profile4_node67_cert).mp (by decide +kernel))

def profile4_node68_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 43 19 38 28 20 32), lower := (rows 43 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 49 60 40 48 32) }] }

theorem profile4_node68 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,34] 6 20 profile4_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,34] 6 20 profile4_node68_cert).mp (by decide +kernel))

def profile4_node69_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 43 19 52 14 22 32), lower := (rows 43 19 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 45 53 52 40 52 32) }] }

theorem profile4_node69 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,48] 6 6 profile4_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17,48] 6 6 profile4_node69_cert).mp (by decide +kernel))

def profile4_node66_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node66_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node66 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,17] 6 (by decide) (choices 2) [18,34,48] profile4_node66_route profile4_node66_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node67
  · exact profile4_node68
  · exact profile4_node69

def profile4_node71_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 43 22 7 60 52 32), lower := (rows 43 22 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 60 61 40 48 32) }] }

theorem profile4_node71 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,3] 6 52 profile4_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,3] 6 52 profile4_node71_cert).mp (by decide +kernel))

def profile4_node72_cert : CutBound 6 := { lost := (rows 16 0 0 16 0 0), upper := (rows 43 22 21 46 54 32), lower := (rows 43 22 21 8 16 32), losses := [{ target := 4, region := (rows 3 2 4 10 0 63), good := (rows 43 47 37 40 32 32) }] }

theorem profile4_node72 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,17] 6 38 profile4_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,17] 6 38 profile4_node72_cert).mp (by decide +kernel))

def profile4_node73_cert : CutBound 6 := { lost := (rows 16 0 0 16 0 0), upper := (rows 43 22 22 45 53 32), lower := (rows 43 22 22 8 16 32), losses := [{ target := 4, region := (rows 7 2 4 14 0 63), good := (rows 43 47 47 40 32 32) }] }

theorem profile4_node73 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,18] 6 37 profile4_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,18] 6 37 profile4_node73_cert).mp (by decide +kernel))

def profile4_node74_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 43 22 37 30 22 32), lower := (rows 43 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 45 52 37 40 48 32) }] }

theorem profile4_node74 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,33] 6 22 profile4_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,33] 6 22 profile4_node74_cert).mp (by decide +kernel))

def profile4_node75_cert : CutBound 6 := { lost := (rows 0 0 16 0 0 0), upper := (rows 43 22 38 29 21 32), lower := (rows 43 22 38 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 8 0 63), good := (rows 47 38 38 40 32 32) }] }

theorem profile4_node75 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,34] 6 21 profile4_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,34] 6 21 profile4_node75_cert).mp (by decide +kernel))

def profile4_node76_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 43 22 52 15 23 32), lower := (rows 43 22 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 45 52 52 40 52 32) }] }

theorem profile4_node76 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,48] 6 7 profile4_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20,48] 6 7 profile4_node76_cert).mp (by decide +kernel))

def profile4_node70_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node70_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node70 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,20] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile4_node70_route profile4_node70_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node71
  · exact profile4_node72
  · exact profile4_node73
  · exact profile4_node74
  · exact profile4_node75
  · exact profile4_node76

def profile4_node77_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 43 35 22 30 22 32), lower := (rows 43 35 4 8 16 32), losses := [{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 32 43 48 32) }] }

theorem profile4_node77 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,33] 6 22 profile4_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,33] 6 22 profile4_node77_cert).mp (by decide +kernel))

def profile4_node78_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 43 38 23 31 23 32), lower := (rows 43 38 4 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 63), good := (rows 43 38 38 40 32 32) }] }

theorem profile4_node78 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,36] 6 23 profile4_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,36] 6 23 profile4_node78_cert).mp (by decide +kernel))

def profile4_node79_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 43 50 23 31 23 32), lower := (rows 43 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 43 50 32 40 50 32) }] }

theorem profile4_node79 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,48] 6 23 profile4_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42,48] 6 23 profile4_node79_cert).mp (by decide +kernel))

def profile4_node61_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node61_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node61 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [42] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile4_node61_route profile4_node61_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node62
  · exact profile4_node66
  · exact profile4_node70
  · exact profile4_node77
  · exact profile4_node78
  · exact profile4_node79

def profile4_node82_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 7 14 60 52 32), lower := (rows 51 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node82 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,10] 6 52 profile4_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,10] 6 52 profile4_node82_cert).mp (by decide +kernel))

def profile4_node83_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 7 22 44 60 32), lower := (rows 51 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node83 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,18] 6 44 profile4_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,18] 6 44 profile4_node83_cert).mp (by decide +kernel))

def profile4_node84_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 51 7 28 46 54 32), lower := (rows 51 7 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 63), good := (rows 43 47 44 40 32 32) }] }

theorem profile4_node84 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,24] 6 38 profile4_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,24] 6 38 profile4_node84_cert).mp (by decide +kernel))

def profile4_node85_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 7 38 28 28 32), lower := (rows 51 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile4_node85 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,34] 6 28 profile4_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,34] 6 28 profile4_node85_cert).mp (by decide +kernel))

def profile4_node86_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 7 44 30 22 32), lower := (rows 51 7 44 8 16 32), losses := [{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 49 37 44 44 48 32) }] }

theorem profile4_node86 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,40] 6 22 profile4_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,40] 6 22 profile4_node86_cert).mp (by decide +kernel))

def profile4_node87_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 7 52 14 30 32), lower := (rows 51 7 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 53 37 52 40 52 32) }] }

theorem profile4_node87 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,48] 6 14 profile4_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5,48] 6 14 profile4_node87_cert).mp (by decide +kernel))

def profile4_node81_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | _ => 0

def profile4_node81_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node81 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,5] 6 (by decide) (choices 2) [10,18,24,34,40,48] profile4_node81_route profile4_node81_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node82
  · exact profile4_node83
  · exact profile4_node84
  · exact profile4_node85
  · exact profile4_node86
  · exact profile4_node87

def profile4_node89_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 11 22 44 52 32), lower := (rows 51 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 49 41 60 40 48 32) }] }

theorem profile4_node89 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,18] 6 36 profile4_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,18] 6 36 profile4_node89_cert).mp (by decide +kernel))

def profile4_node90_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 11 38 28 20 32), lower := (rows 51 11 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 49 41 60 40 48 32) }] }

theorem profile4_node90 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,34] 6 20 profile4_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,34] 6 20 profile4_node90_cert).mp (by decide +kernel))

def profile4_node91_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 11 52 14 22 32), lower := (rows 51 11 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 53 45 52 40 52 32) }] }

theorem profile4_node91 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,48] 6 6 profile4_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9,48] 6 6 profile4_node91_cert).mp (by decide +kernel))

def profile4_node88_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node88_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node88 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,9] 6 (by decide) (choices 2) [18,34,48] profile4_node88_route profile4_node88_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node89
  · exact profile4_node90
  · exact profile4_node91

def profile4_node93_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 14 7 60 52 32), lower := (rows 51 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 60 61 40 48 32) }] }

theorem profile4_node93 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,3] 6 52 profile4_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,3] 6 52 profile4_node93_cert).mp (by decide +kernel))

def profile4_node94_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 14 21 46 54 32), lower := (rows 51 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 53 44 53 40 48 32) }] }

theorem profile4_node94 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,17] 6 38 profile4_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,17] 6 38 profile4_node94_cert).mp (by decide +kernel))

def profile4_node95_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 51 14 22 45 53 32), lower := (rows 51 14 22 8 16 32), losses := [{ target := 2, region := (rows 5 2 0 8 16 63), good := (rows 51 43 51 40 48 32) }] }

theorem profile4_node95 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,18] 6 37 profile4_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,18] 6 37 profile4_node95_cert).mp (by decide +kernel))

def profile4_node96_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 14 37 30 22 32), lower := (rows 51 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 53 44 37 40 48 32) }] }

theorem profile4_node96 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,33] 6 22 profile4_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,33] 6 22 profile4_node96_cert).mp (by decide +kernel))

def profile4_node97_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 51 14 38 29 21 32), lower := (rows 51 14 38 8 16 32), losses := [{ target := 4, region := (rows 1 10 15 8 0 63), good := (rows 39 46 38 46 32 32) }] }

theorem profile4_node97 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,34] 6 21 profile4_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,34] 6 21 profile4_node97_cert).mp (by decide +kernel))

def profile4_node98_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 14 52 15 23 32), lower := (rows 51 14 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 53 44 52 40 52 32) }] }

theorem profile4_node98 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,48] 6 7 profile4_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12,48] 6 7 profile4_node98_cert).mp (by decide +kernel))

def profile4_node92_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node92 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,12] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile4_node92_route profile4_node92_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node93
  · exact profile4_node94
  · exact profile4_node95
  · exact profile4_node96
  · exact profile4_node97
  · exact profile4_node98

def profile4_node99_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 51 19 46 46 62 32), lower := (rows 51 19 4 8 16 32), losses := [{ target := 2, region := (rows 19 19 0 8 16 63), good := (rows 51 51 32 40 51 32) }] }

theorem profile4_node99 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,17] 6 46 profile4_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,17] 6 46 profile4_node99_cert).mp (by decide +kernel))

def profile4_node100_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 51 22 47 47 63 32), lower := (rows 51 22 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 51 51 32 40 48 32) }] }

theorem profile4_node100 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,20] 6 47 profile4_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,20] 6 47 profile4_node100_cert).mp (by decide +kernel))

def profile4_node101_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 51 26 39 47 55 32), lower := (rows 51 26 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 51 59 32 40 48 32) }] }

theorem profile4_node101 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,24] 6 39 profile4_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,24] 6 39 profile4_node101_cert).mp (by decide +kernel))

def profile4_node102_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 51 35 30 30 30 32), lower := (rows 51 35 4 8 16 32), losses := [{ target := 2, region := (rows 17 19 0 8 16 63), good := (rows 51 35 32 40 51 32) }] }

theorem profile4_node102 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,33] 6 30 profile4_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,33] 6 30 profile4_node102_cert).mp (by decide +kernel))

def profile4_node103_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 51 38 31 31 31 32), lower := (rows 51 38 4 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 63), good := (rows 35 38 38 40 32 32) }] }

theorem profile4_node103 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,36] 6 31 profile4_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,36] 6 31 profile4_node103_cert).mp (by decide +kernel))

def profile4_node104_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 51 42 23 31 23 32), lower := (rows 51 42 4 8 16 32), losses := [{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 51 42 32 42 48 32) }] }

theorem profile4_node104 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,40] 6 23 profile4_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,40] 6 23 profile4_node104_cert).mp (by decide +kernel))

def profile4_node105_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 51 50 15 15 31 32), lower := (rows 51 50 4 8 16 32), losses := [{ target := 2, region := (rows 19 19 0 8 16 63), good := (rows 51 51 32 40 51 32) }] }

theorem profile4_node105 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,48] 6 15 profile4_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50,48] 6 15 profile4_node105_cert).mp (by decide +kernel))

def profile4_node80_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile4_node80_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node80 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [50] 6 (by decide) (choices 2) [5,9,12,17,20,24,33,36,40,48] profile4_node80_route profile4_node80_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node81
  · exact profile4_node88
  · exact profile4_node92
  · exact profile4_node99
  · exact profile4_node100
  · exact profile4_node101
  · exact profile4_node102
  · exact profile4_node103
  · exact profile4_node104
  · exact profile4_node105

def profile4_node108_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 57 7 22 46 54 32), lower := (rows 57 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 14 0 63), good := (rows 41 47 46 40 32 32) }] }

theorem profile4_node108 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,18] 6 38 profile4_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,18] 6 38 profile4_node108_cert).mp (by decide +kernel))

def profile4_node109_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 57 7 38 30 22 32), lower := (rows 57 7 38 8 16 32), losses := [{ target := 4, region := (rows 1 3 7 8 0 63), good := (rows 47 39 38 40 32 32) }] }

theorem profile4_node109 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,34] 6 22 profile4_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,34] 6 22 profile4_node109_cert).mp (by decide +kernel))

def profile4_node110_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 57 7 52 14 22 32), lower := (rows 57 7 52 8 16 32), losses := [{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 61 37 52 40 52 32) }] }

theorem profile4_node110 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,48] 6 6 profile4_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5,48] 6 6 profile4_node110_cert).mp (by decide +kernel))

def profile4_node107_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node107_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node107 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,5] 6 (by decide) (choices 2) [18,34,48] profile4_node107_route profile4_node107_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node108
  · exact profile4_node109
  · exact profile4_node110

def profile4_node111_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 57 19 38 46 54 32), lower := (rows 57 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 59 51 32 40 48 32) }] }

theorem profile4_node111 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,17] 6 38 profile4_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,17] 6 38 profile4_node111_cert).mp (by decide +kernel))

def profile4_node113_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 57 22 7 46 54 32), lower := (rows 57 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 14 0 63), good := (rows 41 46 47 40 32 32) }] }

theorem profile4_node113 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,3] 6 38 profile4_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,3] 6 38 profile4_node113_cert).mp (by decide +kernel))

def profile4_node114_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 57 22 37 14 22 32), lower := (rows 57 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 61 52 37 40 48 32) }] }

theorem profile4_node114 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,33] 6 6 profile4_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,33] 6 6 profile4_node114_cert).mp (by decide +kernel))

def profile4_node115_cert : CutBound 6 := { lost := (rows 0 0 16 0 0 0), upper := (rows 57 22 38 15 23 32), lower := (rows 57 22 38 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 8 0 63), good := (rows 41 38 38 40 32 32) }] }

theorem profile4_node115 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,34] 6 7 profile4_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20,34] 6 7 profile4_node115_cert).mp (by decide +kernel))

def profile4_node112_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile4_node112_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node112 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,20] 6 (by decide) (choices 2) [3,33,34] profile4_node112_route profile4_node112_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node113
  · exact profile4_node114
  · exact profile4_node115

def profile4_node116_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 57 35 22 30 22 32), lower := (rows 57 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 59 35 32 40 48 32) }] }

theorem profile4_node116 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,33] 6 22 profile4_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,33] 6 22 profile4_node116_cert).mp (by decide +kernel))

def profile4_node117_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 57 38 23 31 23 32), lower := (rows 57 38 4 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 63), good := (rows 41 38 38 40 32 32) }] }

theorem profile4_node117 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,36] 6 23 profile4_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,36] 6 23 profile4_node117_cert).mp (by decide +kernel))

def profile4_node118_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 57 50 7 15 23 32), lower := (rows 57 50 4 8 16 32), losses := [{ target := 2, region := (rows 1 19 0 8 16 63), good := (rows 59 50 32 40 50 32) }] }

theorem profile4_node118 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,48] 6 7 profile4_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56,48] 6 7 profile4_node118_cert).mp (by decide +kernel))

def profile4_node106_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile4_node106_route : Route 6 := (fun mask => (mask,id))

theorem profile4_node106 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [56] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile4_node106_route profile4_node106_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node107
  · exact profile4_node111
  · exact profile4_node112
  · exact profile4_node116
  · exact profile4_node117
  · exact profile4_node118

def profile4_node0_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile4_node0_route : Route 6 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 44 => (42,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [] 6 (by decide) (choices 3) [14,22,26,38,42,50,56] profile4_node0_route profile4_node0_column
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node11
  · exact profile4_node25
  · exact profile4_node35
  · exact profile4_node61
  · exact profile4_node80
  · exact profile4_node106

theorem profile4 : Upper (D (n:=6) [49,34,34,33,18,2]) (R (n:=6) [49,34,34,33,18,2]) [] 6 := profile4_node0


#print axioms profile4
end Delivery.SmallBudgetTenFinite6
