import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile9_node2_cert : CutBound 6 := { lost := (rows 32 32 0 4 4 0), upper := (rows 7 7 63 59 59 32), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) },{ target := 5, region := (rows 7 7 4 8 16 0), good := (rows 7 7 7 8 16 0) }] }

theorem profile9_node2 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,5] 6 59 profile9_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,5] 6 59 profile9_node2_cert).mp (by decide +kernel))

def profile9_node4_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 7 11 7 60 52 32), lower := (rows 7 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 63), good := (rows 62 58 62 40 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) }] }

theorem profile9_node4 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,3] 6 52 profile9_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,3] 6 52 profile9_node4_cert).mp (by decide +kernel))

def profile9_node6_cert : CutBound 6 := { lost := (rows 0 0 2 1 3 0), upper := (rows 7 11 21 42 52 32), lower := (rows 7 11 21 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 21 63), good := (rows 62 58 60 42 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 53 61 53 60 48 32) }] }

theorem profile9_node6 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,34] 6 36 profile9_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,34] 6 36 profile9_node6_cert).mp (by decide +kernel))

def profile9_node7_cert : CutBound 6 := { lost := (rows 0 0 0 3 1 0), upper := (rows 7 11 21 44 50 32), lower := (rows 7 11 21 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 19 63), good := (rows 62 58 60 44 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 45 41 61 44 48 32) }] }

theorem profile9_node7 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,36] 6 34 profile9_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17,36] 6 34 profile9_node7_cert).mp (by decide +kernel))

def profile9_node5_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 5 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node5 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,17] 6 (by decide) (choices 2) [34,36] profile9_node5_route profile9_node5_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node6
  · exact profile9_node7

def profile9_node8_cert : CutBound 6 := { lost := (rows 32 0 0 2 2 0), upper := (rows 7 11 22 45 53 32), lower := (rows 7 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 52 40 48 32) },{ target := 5, region := (rows 5 2 4 8 16 0), good := (rows 7 11 23 8 16 0) }] }

theorem profile9_node8 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,18] 6 37 profile9_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,18] 6 37 profile9_node8_cert).mp (by decide +kernel))

def profile9_node9_cert : CutBound 6 := { lost := (rows 0 0 2 1 1 0), upper := (rows 7 11 37 62 54 32), lower := (rows 7 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 45 37 40 48 32) }] }

theorem profile9_node9 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,33] 6 54 profile9_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,33] 6 54 profile9_node9_cert).mp (by decide +kernel))

def profile9_node10_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 7 11 38 61 53 32), lower := (rows 7 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 46 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) }] }

theorem profile9_node10 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,34] 6 53 profile9_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,34] 6 53 profile9_node10_cert).mp (by decide +kernel))

def profile9_node12_cert : CutBound 6 := { lost := (rows 0 0 3 0 3 0), upper := (rows 7 11 52 11 52 32), lower := (rows 7 11 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 62 52 62 52 52) },{ target := 1, region := (rows 1 0 63 8 63 63), good := (rows 53 61 52 61 52 52) }] }

theorem profile9_node12 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,3] 6 36 profile9_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,3] 6 36 profile9_node12_cert).mp (by decide +kernel))

def profile9_node13_cert : CutBound 6 := { lost := (rows 0 0 3 2 1 0), upper := (rows 7 11 52 13 50 32), lower := (rows 7 11 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 31 8 19 63), good := (rows 54 62 52 60 52 32) },{ target := 1, region := (rows 1 0 20 9 16 63), good := (rows 45 41 52 45 52 32) }] }

theorem profile9_node13 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,5] 6 34 profile9_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,5] 6 34 profile9_node13_cert).mp (by decide +kernel))

def profile9_node14_cert : CutBound 6 := { lost := (rows 0 0 3 1 2 0), upper := (rows 7 11 52 14 49 32), lower := (rows 7 11 52 14 16 32), losses := [{ target := 0, region := (rows 0 2 20 9 16 63), good := (rows 46 42 52 46 52 32) },{ target := 1, region := (rows 1 0 31 8 19 63), good := (rows 53 61 52 60 52 32) }] }

theorem profile9_node14 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,6] 6 33 profile9_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,6] 6 33 profile9_node14_cert).mp (by decide +kernel))

def profile9_node15_cert : CutBound 6 := { lost := (rows 0 0 3 2 1 0), upper := (rows 7 11 52 41 22 32), lower := (rows 7 11 52 41 16 32), losses := [{ target := 0, region := (rows 0 2 31 8 19 63), good := (rows 54 62 52 60 52 32) },{ target := 1, region := (rows 1 0 20 11 16 63), good := (rows 45 41 52 41 52 32) }] }

theorem profile9_node15 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,33] 6 6 profile9_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,33] 6 6 profile9_node15_cert).mp (by decide +kernel))

def profile9_node16_cert : CutBound 6 := { lost := (rows 0 0 3 1 2 0), upper := (rows 7 11 52 42 21 32), lower := (rows 7 11 52 42 16 32), losses := [{ target := 0, region := (rows 0 2 20 11 16 63), good := (rows 46 42 52 42 52 32) },{ target := 1, region := (rows 1 0 31 8 19 63), good := (rows 53 61 52 60 52 32) }] }

theorem profile9_node16 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,34] 6 5 profile9_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,34] 6 5 profile9_node16_cert).mp (by decide +kernel))

def profile9_node17_cert : CutBound 6 := { lost := (rows 0 0 3 3 0 0), upper := (rows 7 11 52 44 19 32), lower := (rows 7 11 52 44 16 32), losses := [{ target := 0, region := (rows 0 2 20 29 16 63), good := (rows 46 42 60 44 60 32) },{ target := 1, region := (rows 1 0 20 29 16 63), good := (rows 45 41 60 44 60 32) }] }

theorem profile9_node17 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,36] 6 3 profile9_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48,36] 6 3 profile9_node17_cert).mp (by decide +kernel))

def profile9_node11_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node11 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9,48] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node11_route profile9_node11_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node12
  · exact profile9_node13
  · exact profile9_node14
  · exact profile9_node15
  · exact profile9_node16
  · exact profile9_node17

def profile9_node3_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node3 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node3_route profile9_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node4
  · exact profile9_node5
  · exact profile9_node8
  · exact profile9_node9
  · exact profile9_node10
  · exact profile9_node11

def profile9_node18_cert : CutBound 6 := { lost := (rows 32 0 0 4 4 0), upper := (rows 7 14 55 59 51 32), lower := (rows 7 14 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 32 40 48 32) },{ target := 5, region := (rows 3 2 4 8 16 0), good := (rows 7 15 4 8 16 0) }] }

theorem profile9_node18 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,12] 6 51 profile9_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,12] 6 51 profile9_node18_cert).mp (by decide +kernel))

def profile9_node20_cert : CutBound 6 := { lost := (rows 32 0 32 2 2 0), upper := (rows 7 26 7 45 53 32), lower := (rows 7 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 56 61 40 48 32) },{ target := 5, region := (rows 7 2 7 8 16 0), good := (rows 7 31 7 8 16 0) }] }

theorem profile9_node20 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,3] 6 37 profile9_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,3] 6 37 profile9_node20_cert).mp (by decide +kernel))

def profile9_node22_cert : CutBound 6 := { lost := (rows 0 1 2 0 3 0), upper := (rows 7 26 37 11 52 32), lower := (rows 7 26 37 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 21 63), good := (rows 54 58 52 58 48 32) },{ target := 1, region := (rows 1 0 13 8 31 63), good := (rows 53 60 53 61 48 32) }] }

theorem profile9_node22 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,3] 6 36 profile9_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,3] 6 36 profile9_node22_cert).mp (by decide +kernel))

def profile9_node23_cert : CutBound 6 := { lost := (rows 0 1 2 2 1 0), upper := (rows 7 26 37 13 50 32), lower := (rows 7 26 37 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 63), good := (rows 54 58 52 62 48 32) },{ target := 1, region := (rows 1 0 13 13 16 63), good := (rows 45 60 45 45 48 32) }] }

theorem profile9_node23 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,5] 6 34 profile9_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,5] 6 34 profile9_node23_cert).mp (by decide +kernel))

def profile9_node24_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 7 26 37 14 49 32), lower := (rows 7 26 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 63), good := (rows 46 58 44 46 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 56 53 60 48 32) }] }

theorem profile9_node24 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,6] 6 33 profile9_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,6] 6 33 profile9_node24_cert).mp (by decide +kernel))

def profile9_node25_cert : CutBound 6 := { lost := (rows 0 1 2 2 1 0), upper := (rows 7 26 37 41 22 32), lower := (rows 7 26 37 41 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 17 63), good := (rows 54 58 52 58 48 32) },{ target := 1, region := (rows 1 0 13 13 16 63), good := (rows 45 60 45 45 48 32) }] }

theorem profile9_node25 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,33] 6 6 profile9_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,33] 6 6 profile9_node25_cert).mp (by decide +kernel))

def profile9_node26_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 7 26 37 42 21 32), lower := (rows 7 26 37 42 16 32), losses := [{ target := 0, region := (rows 0 18 4 27 16 63), good := (rows 46 58 44 42 58 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 56 53 40 48 32) }] }

theorem profile9_node26 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,34] 6 5 profile9_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,34] 6 5 profile9_node26_cert).mp (by decide +kernel))

def profile9_node27_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 7 26 37 44 19 32), lower := (rows 7 26 37 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 16 63), good := (rows 46 58 44 44 48 32) },{ target := 1, region := (rows 1 0 5 13 16 63), good := (rows 45 56 45 44 48 32) }] }

theorem profile9_node27 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,36] 6 3 profile9_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33,36] 6 3 profile9_node27_cert).mp (by decide +kernel))

def profile9_node21_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node21 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,33] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node21_route profile9_node21_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node22
  · exact profile9_node23
  · exact profile9_node24
  · exact profile9_node25
  · exact profile9_node26
  · exact profile9_node27

def profile9_node28_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 7 26 38 45 53 32), lower := (rows 7 26 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 62 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 56 36 40 48 32) }] }

theorem profile9_node28 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,34] 6 37 profile9_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24,34] 6 37 profile9_node28_cert).mp (by decide +kernel))

def profile9_node19_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node19_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node19 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,24] 6 (by decide) (choices 2) [3,33,34] profile9_node19_route profile9_node19_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node20
  · exact profile9_node21
  · exact profile9_node28

def profile9_node30_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 7 35 7 60 60 32), lower := (rows 7 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 63), good := (rows 62 58 62 40 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) }] }

theorem profile9_node30 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,3] 6 60 profile9_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,3] 6 60 profile9_node30_cert).mp (by decide +kernel))

def profile9_node31_cert : CutBound 6 := { lost := (rows 0 4 0 1 1 0), upper := (rows 7 35 13 62 54 32), lower := (rows 7 35 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 35 35 43 40 48 32) }] }

theorem profile9_node31 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,9] 6 54 profile9_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,9] 6 54 profile9_node31_cert).mp (by decide +kernel))

def profile9_node32_cert : CutBound 6 := { lost := (rows 0 4 0 2 2 0), upper := (rows 7 35 14 61 53 32), lower := (rows 7 35 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 44 40 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 42 40 48 32) }] }

theorem profile9_node32 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,10] 6 53 profile9_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,10] 6 53 profile9_node32_cert).mp (by decide +kernel))

def profile9_node34_cert : CutBound 6 := { lost := (rows 0 0 3 0 3 0), upper := (rows 7 35 28 11 52 32), lower := (rows 7 35 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 29 63), good := (rows 54 50 60 62 48 32) },{ target := 1, region := (rows 1 0 12 8 29 63), good := (rows 53 49 60 61 48 32) }] }

theorem profile9_node34 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,3] 6 36 profile9_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,3] 6 36 profile9_node34_cert).mp (by decide +kernel))

def profile9_node35_cert : CutBound 6 := { lost := (rows 0 0 1 2 1 0), upper := (rows 7 35 28 13 50 32), lower := (rows 7 35 28 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 63), good := (rows 54 50 60 60 48 32) },{ target := 1, region := (rows 1 0 4 9 16 63), good := (rows 45 41 60 45 48 32) }] }

theorem profile9_node35 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,5] 6 34 profile9_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,5] 6 34 profile9_node35_cert).mp (by decide +kernel))

def profile9_node36_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 7 35 28 14 49 32), lower := (rows 7 35 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 63), good := (rows 46 42 60 46 48 32) },{ target := 1, region := (rows 1 0 12 8 19 63), good := (rows 53 49 60 60 48 32) }] }

theorem profile9_node36 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,6] 6 33 profile9_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,6] 6 33 profile9_node36_cert).mp (by decide +kernel))

def profile9_node37_cert : CutBound 6 := { lost := (rows 0 0 1 2 1 0), upper := (rows 7 35 28 41 22 32), lower := (rows 7 35 28 41 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 17 63), good := (rows 54 50 60 60 48 32) },{ target := 1, region := (rows 1 0 4 11 16 63), good := (rows 45 41 60 41 48 32) }] }

theorem profile9_node37 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,33] 6 6 profile9_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,33] 6 6 profile9_node37_cert).mp (by decide +kernel))

def profile9_node38_cert : CutBound 6 := { lost := (rows 0 4 0 5 2 0), upper := (rows 7 35 28 42 21 32), lower := (rows 7 35 28 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 16 63), good := (rows 46 42 60 42 48 32) },{ target := 1, region := (rows 1 0 4 8 17 63), good := (rows 53 49 60 40 48 32) },{ target := 2, region := (rows 1 3 0 11 16 63), good := (rows 43 43 56 42 48 32) }] }

theorem profile9_node38 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,34] 6 5 profile9_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,34] 6 5 profile9_node38_cert).mp (by decide +kernel))

def profile9_node39_cert : CutBound 6 := { lost := (rows 0 0 3 3 0 0), upper := (rows 7 35 28 44 19 32), lower := (rows 7 35 28 44 16 32), losses := [{ target := 0, region := (rows 0 2 20 29 16 63), good := (rows 46 42 60 44 60 32) },{ target := 1, region := (rows 1 0 20 29 16 63), good := (rows 45 41 60 44 60 32) }] }

theorem profile9_node39 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,36] 6 3 profile9_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24,36] 6 3 profile9_node39_cert).mp (by decide +kernel))

def profile9_node33_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node33 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,24] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node33_route profile9_node33_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node34
  · exact profile9_node35
  · exact profile9_node36
  · exact profile9_node37
  · exact profile9_node38
  · exact profile9_node39

def profile9_node40_cert : CutBound 6 := { lost := (rows 0 0 2 1 1 0), upper := (rows 7 35 37 30 30 32), lower := (rows 7 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) }] }

theorem profile9_node40 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,33] 6 30 profile9_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,33] 6 30 profile9_node40_cert).mp (by decide +kernel))

def profile9_node41_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 7 35 38 29 29 32), lower := (rows 7 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) }] }

theorem profile9_node41 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,34] 6 29 profile9_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,34] 6 29 profile9_node41_cert).mp (by decide +kernel))

def profile9_node42_cert : CutBound 6 := { lost := (rows 0 4 3 0 0 0), upper := (rows 7 35 44 31 23 32), lower := (rows 7 35 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 38 34 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 37 33 44 44 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 40 40 48 32) }] }

theorem profile9_node42 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,40] 6 23 profile9_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33,40] 6 23 profile9_node42_cert).mp (by decide +kernel))

def profile9_node29_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile9_node29_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile9_node29 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,33] 6 (by decide) (choices 2) [3,9,10,24,33,34,40] profile9_node29_route profile9_node29_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node30
  · exact profile9_node31
  · exact profile9_node32
  · exact profile9_node33
  · exact profile9_node40
  · exact profile9_node41
  · exact profile9_node42

def profile9_node43_cert : CutBound 6 := { lost := (rows 0 1 0 4 4 0), upper := (rows 7 38 63 59 59 32), lower := (rows 7 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile9_node43 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,36] 6 59 profile9_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,36] 6 59 profile9_node43_cert).mp (by decide +kernel))

def profile9_node45_cert : CutBound 6 := { lost := (rows 0 1 0 2 2 0), upper := (rows 7 42 7 61 53 32), lower := (rows 7 42 7 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 38 42 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 40 61 40 48 32) }] }

theorem profile9_node45 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,3] 6 53 profile9_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,3] 6 53 profile9_node45_cert).mp (by decide +kernel))

def profile9_node47_cert : CutBound 6 := { lost := (rows 0 1 2 0 3 0), upper := (rows 7 42 21 11 52 32), lower := (rows 7 42 21 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 21 63), good := (rows 54 42 52 58 48 32) },{ target := 1, region := (rows 1 0 13 8 31 63), good := (rows 53 60 53 61 48 32) }] }

theorem profile9_node47 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,3] 6 36 profile9_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,3] 6 36 profile9_node47_cert).mp (by decide +kernel))

def profile9_node48_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 7 42 21 13 50 32), lower := (rows 7 42 21 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 63), good := (rows 54 58 52 62 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 45 40 61 45 48 32) }] }

theorem profile9_node48 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,5] 6 34 profile9_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,5] 6 34 profile9_node48_cert).mp (by decide +kernel))

def profile9_node49_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 7 42 21 14 49 32), lower := (rows 7 42 21 14 16 32), losses := [{ target := 0, region := (rows 0 15 4 13 16 63), good := (rows 46 42 62 46 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 40 53 60 48 32) }] }

theorem profile9_node49 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,6] 6 33 profile9_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,6] 6 33 profile9_node49_cert).mp (by decide +kernel))

def profile9_node50_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 7 42 21 41 22 32), lower := (rows 7 42 21 41 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 17 63), good := (rows 54 42 52 58 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 45 40 61 41 48 32) }] }

theorem profile9_node50 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,33] 6 6 profile9_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,33] 6 6 profile9_node50_cert).mp (by decide +kernel))

def profile9_node51_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 7 42 21 42 21 32), lower := (rows 7 42 21 42 16 32), losses := [{ target := 0, region := (rows 0 63 4 63 16 63), good := (rows 46 42 62 42 58 42) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 40 53 40 48 32) }] }

theorem profile9_node51 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,34] 6 5 profile9_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,34] 6 5 profile9_node51_cert).mp (by decide +kernel))

def profile9_node52_cert : CutBound 6 := { lost := (rows 0 1 0 3 0 0), upper := (rows 7 42 21 44 19 32), lower := (rows 7 42 21 44 16 32), losses := [{ target := 0, region := (rows 0 15 4 13 16 63), good := (rows 46 42 62 46 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 45 40 61 44 48 32) }] }

theorem profile9_node52 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,36] 6 3 profile9_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17,36] 6 3 profile9_node52_cert).mp (by decide +kernel))

def profile9_node46_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node46_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node46 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,17] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node46_route profile9_node46_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node47
  · exact profile9_node48
  · exact profile9_node49
  · exact profile9_node50
  · exact profile9_node51
  · exact profile9_node52

def profile9_node53_cert : CutBound 6 := { lost := (rows 0 1 0 2 2 0), upper := (rows 7 42 22 45 53 32), lower := (rows 7 42 22 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 54 42 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 40 52 40 48 32) }] }

theorem profile9_node53 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,18] 6 37 profile9_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,18] 6 37 profile9_node53_cert).mp (by decide +kernel))

def profile9_node54_cert : CutBound 6 := { lost := (rows 0 5 2 0 0 0), upper := (rows 7 42 37 31 23 32), lower := (rows 7 42 37 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 36 42 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 40 37 40 48 32) },{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 33 42 48 32) }] }

theorem profile9_node54 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,33] 6 23 profile9_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,33] 6 23 profile9_node54_cert).mp (by decide +kernel))

def profile9_node55_cert : CutBound 6 := { lost := (rows 0 1 1 2 2 0), upper := (rows 7 42 38 29 21 32), lower := (rows 7 42 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 40 36 40 48 32) }] }

theorem profile9_node55 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,34] 6 21 profile9_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,34] 6 21 profile9_node55_cert).mp (by decide +kernel))

def profile9_node56_cert : CutBound 6 := { lost := (rows 0 1 3 0 0 0), upper := (rows 7 42 52 15 23 32), lower := (rows 7 42 52 8 16 32), losses := [{ target := 0, region := (rows 0 10 20 8 16 63), good := (rows 38 42 52 42 52 32) },{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 37 40 52 40 52 32) }] }

theorem profile9_node56 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,48] 6 7 profile9_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40,48] 6 7 profile9_node56_cert).mp (by decide +kernel))

def profile9_node44_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node44 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6,40] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node44_route profile9_node44_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node45
  · exact profile9_node46
  · exact profile9_node53
  · exact profile9_node54
  · exact profile9_node55
  · exact profile9_node56

def profile9_node1_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile9_node1_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile9_node1 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [6] 6 (by decide) (choices 2) [5,9,12,24,33,36,40] profile9_node1_route profile9_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node2
  · exact profile9_node3
  · exact profile9_node18
  · exact profile9_node19
  · exact profile9_node29
  · exact profile9_node43
  · exact profile9_node44

def profile9_node59_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 11 7 7 60 52 32), lower := (rows 11 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 58 62 62 40 48 32) },{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) }] }

theorem profile9_node59 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,3] 6 52 profile9_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,3] 6 52 profile9_node59_cert).mp (by decide +kernel))

def profile9_node60_cert : CutBound 6 := { lost := (rows 0 32 0 1 1 0), upper := (rows 11 7 21 46 54 32), lower := (rows 11 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 52 40 48 32) },{ target := 5, region := (rows 1 6 4 8 16 0), good := (rows 11 7 23 8 16 0) }] }

theorem profile9_node60 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,17] 6 38 profile9_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,17] 6 38 profile9_node60_cert).mp (by decide +kernel))

def profile9_node62_cert : CutBound 6 := { lost := (rows 0 0 1 2 3 0), upper := (rows 11 7 22 41 52 32), lower := (rows 11 7 22 41 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 62 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 11 22 63), good := (rows 57 61 60 41 48 32) }] }

theorem profile9_node62 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,33] 6 36 profile9_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,33] 6 36 profile9_node62_cert).mp (by decide +kernel))

def profile9_node63_cert : CutBound 6 := { lost := (rows 0 0 0 3 2 0), upper := (rows 11 7 22 44 49 32), lower := (rows 11 7 22 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 42 46 62 44 48 32) },{ target := 1, region := (rows 1 0 4 14 19 63), good := (rows 57 61 60 44 48 32) }] }

theorem profile9_node63 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,36] 6 33 profile9_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18,36] 6 33 profile9_node63_cert).mp (by decide +kernel))

def profile9_node61_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 5 => 5 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node61_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node61 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,18] 6 (by decide) (choices 2) [33,36] profile9_node61_route profile9_node61_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node62
  · exact profile9_node63

def profile9_node64_cert : CutBound 6 := { lost := (rows 0 0 2 1 1 0), upper := (rows 11 7 37 62 54 32), lower := (rows 11 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 36 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 45 37 37 40 48 32) }] }

theorem profile9_node64 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,33] 6 54 profile9_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,33] 6 54 profile9_node64_cert).mp (by decide +kernel))

def profile9_node65_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 11 7 38 61 53 32), lower := (rows 11 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 46 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile9_node65 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,34] 6 53 profile9_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,34] 6 53 profile9_node65_cert).mp (by decide +kernel))

def profile9_node67_cert : CutBound 6 := { lost := (rows 0 0 3 0 3 0), upper := (rows 11 7 52 11 52 32), lower := (rows 11 7 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 62 54 52 62 52 52) },{ target := 1, region := (rows 1 0 63 8 63 63), good := (rows 61 53 52 61 52 52) }] }

theorem profile9_node67 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,3] 6 36 profile9_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,3] 6 36 profile9_node67_cert).mp (by decide +kernel))

def profile9_node68_cert : CutBound 6 := { lost := (rows 0 0 3 2 1 0), upper := (rows 11 7 52 13 50 32), lower := (rows 11 7 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 31 8 19 63), good := (rows 62 54 52 60 52 32) },{ target := 1, region := (rows 1 0 20 10 16 63), good := (rows 41 45 52 45 52 32) }] }

theorem profile9_node68 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,5] 6 34 profile9_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,5] 6 34 profile9_node68_cert).mp (by decide +kernel))

def profile9_node69_cert : CutBound 6 := { lost := (rows 0 0 3 1 2 0), upper := (rows 11 7 52 14 49 32), lower := (rows 11 7 52 14 16 32), losses := [{ target := 0, region := (rows 0 2 20 10 16 63), good := (rows 42 46 52 46 52 32) },{ target := 1, region := (rows 1 0 31 8 19 63), good := (rows 61 53 52 60 52 32) }] }

theorem profile9_node69 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,6] 6 33 profile9_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,6] 6 33 profile9_node69_cert).mp (by decide +kernel))

def profile9_node70_cert : CutBound 6 := { lost := (rows 0 0 3 2 1 0), upper := (rows 11 7 52 41 22 32), lower := (rows 11 7 52 41 16 32), losses := [{ target := 0, region := (rows 0 2 31 8 19 63), good := (rows 62 54 52 60 52 32) },{ target := 1, region := (rows 1 0 20 11 16 63), good := (rows 41 45 52 41 52 32) }] }

theorem profile9_node70 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,33] 6 6 profile9_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,33] 6 6 profile9_node70_cert).mp (by decide +kernel))

def profile9_node71_cert : CutBound 6 := { lost := (rows 0 0 3 1 2 0), upper := (rows 11 7 52 42 21 32), lower := (rows 11 7 52 42 16 32), losses := [{ target := 0, region := (rows 0 2 20 11 16 63), good := (rows 42 46 52 42 52 32) },{ target := 1, region := (rows 1 0 31 8 19 63), good := (rows 61 53 52 60 52 32) }] }

theorem profile9_node71 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,34] 6 5 profile9_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,34] 6 5 profile9_node71_cert).mp (by decide +kernel))

def profile9_node72_cert : CutBound 6 := { lost := (rows 0 0 3 3 0 0), upper := (rows 11 7 52 44 19 32), lower := (rows 11 7 52 44 16 32), losses := [{ target := 0, region := (rows 0 2 20 30 16 63), good := (rows 42 46 60 44 60 32) },{ target := 1, region := (rows 1 0 20 30 16 63), good := (rows 41 45 60 44 60 32) }] }

theorem profile9_node72 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,36] 6 3 profile9_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48,36] 6 3 profile9_node72_cert).mp (by decide +kernel))

def profile9_node66_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node66_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node66 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5,48] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node66_route profile9_node66_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node67
  · exact profile9_node68
  · exact profile9_node69
  · exact profile9_node70
  · exact profile9_node71
  · exact profile9_node72

def profile9_node58_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node58_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node58 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node58_route profile9_node58_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node59
  · exact profile9_node60
  · exact profile9_node61
  · exact profile9_node64
  · exact profile9_node65
  · exact profile9_node66

def profile9_node74_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 11 19 7 44 52 32), lower := (rows 11 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 63), good := (rows 42 50 62 40 48 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 49 61 40 48 32) }] }

theorem profile9_node74 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,3] 6 36 profile9_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,3] 6 36 profile9_node74_cert).mp (by decide +kernel))

def profile9_node76_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 11 19 37 14 52 32), lower := (rows 11 19 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 28 63), good := (rows 58 50 52 62 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 61 53 53 60 48 32) }] }

theorem profile9_node76 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,6] 6 36 profile9_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,6] 6 36 profile9_node76_cert).mp (by decide +kernel))

def profile9_node77_cert : CutBound 6 := { lost := (rows 0 0 2 1 3 0), upper := (rows 11 19 37 42 20 32), lower := (rows 11 19 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 20 63), good := (rows 42 58 60 42 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 61 53 53 60 48 32) }] }

theorem profile9_node77 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,34] 6 4 profile9_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,34] 6 4 profile9_node77_cert).mp (by decide +kernel))

def profile9_node78_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 11 19 37 44 22 32), lower := (rows 11 19 37 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 63), good := (rows 42 50 44 44 48 32) },{ target := 1, region := (rows 1 0 7 15 16 63), good := (rows 45 61 45 44 48 32) }] }

theorem profile9_node78 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,36] 6 6 profile9_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33,36] 6 6 profile9_node78_cert).mp (by decide +kernel))

def profile9_node75_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node75_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node75 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,33] 6 (by decide) (choices 2) [6,34,36] profile9_node75_route profile9_node75_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node76
  · exact profile9_node77
  · exact profile9_node78

def profile9_node80_cert : CutBound 6 := { lost := (rows 0 0 1 0 3 0), upper := (rows 11 19 38 13 52 32), lower := (rows 11 19 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 62 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 8 28 63), good := (rows 57 49 52 61 48 32) }] }

theorem profile9_node80 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,5] 6 36 profile9_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,5] 6 36 profile9_node80_cert).mp (by decide +kernel))

def profile9_node81_cert : CutBound 6 := { lost := (rows 0 0 1 2 3 0), upper := (rows 11 19 38 41 20 32), lower := (rows 11 19 38 41 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 62 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 11 20 63), good := (rows 41 57 60 41 48 32) }] }

theorem profile9_node81 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,33] 6 4 profile9_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,33] 6 4 profile9_node81_cert).mp (by decide +kernel))

def profile9_node82_cert : CutBound 6 := { lost := (rows 0 0 1 3 0 0), upper := (rows 11 19 38 44 21 32), lower := (rows 11 19 38 44 16 32), losses := [{ target := 0, region := (rows 0 2 7 15 16 63), good := (rows 46 62 46 44 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 41 49 44 44 48 32) }] }

theorem profile9_node82 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,36] 6 5 profile9_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34,36] 6 5 profile9_node82_cert).mp (by decide +kernel))

def profile9_node79_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node79_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node79 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17,34] 6 (by decide) (choices 2) [5,33,36] profile9_node79_route profile9_node79_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node80
  · exact profile9_node81
  · exact profile9_node82

def profile9_node73_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node73_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node73 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,17] 6 (by decide) (choices 2) [3,33,34] profile9_node73_route profile9_node73_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node74
  · exact profile9_node75
  · exact profile9_node79

def profile9_node84_cert : CutBound 6 := { lost := (rows 0 0 32 2 2 0), upper := (rows 11 22 7 45 53 32), lower := (rows 11 22 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 60 61 40 48 32) },{ target := 5, region := (rows 1 2 5 8 16 0), good := (rows 15 22 7 8 16 0) }] }

theorem profile9_node84 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,3] 6 37 profile9_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,3] 6 37 profile9_node84_cert).mp (by decide +kernel))

def profile9_node86_cert : CutBound 6 := { lost := (rows 0 1 2 0 3 0), upper := (rows 11 22 37 11 52 32), lower := (rows 11 22 37 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 58 54 54 58 48 32) },{ target := 1, region := (rows 1 0 13 8 31 63), good := (rows 61 52 53 61 48 32) }] }

theorem profile9_node86 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,3] 6 36 profile9_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,3] 6 36 profile9_node86_cert).mp (by decide +kernel))

def profile9_node87_cert : CutBound 6 := { lost := (rows 0 1 2 2 1 0), upper := (rows 11 22 37 13 50 32), lower := (rows 11 22 37 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 63), good := (rows 58 54 54 62 48 32) },{ target := 1, region := (rows 1 0 13 13 16 63), good := (rows 45 60 45 45 48 32) }] }

theorem profile9_node87 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,5] 6 34 profile9_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,5] 6 34 profile9_node87_cert).mp (by decide +kernel))

def profile9_node88_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 11 22 37 14 49 32), lower := (rows 11 22 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 63), good := (rows 42 62 36 46 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 61 52 53 60 48 32) }] }

theorem profile9_node88 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,6] 6 33 profile9_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,6] 6 33 profile9_node88_cert).mp (by decide +kernel))

def profile9_node89_cert : CutBound 6 := { lost := (rows 0 1 2 2 1 0), upper := (rows 11 22 37 41 22 32), lower := (rows 11 22 37 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 58 54 54 40 48 32) },{ target := 1, region := (rows 1 0 13 13 16 63), good := (rows 45 60 45 45 48 32) }] }

theorem profile9_node89 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,33] 6 6 profile9_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,33] 6 6 profile9_node89_cert).mp (by decide +kernel))

def profile9_node90_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 11 22 37 42 21 32), lower := (rows 11 22 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 16 63), good := (rows 42 62 44 42 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 61 52 53 40 48 32) }] }

theorem profile9_node90 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,34] 6 5 profile9_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,34] 6 5 profile9_node90_cert).mp (by decide +kernel))

def profile9_node91_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 11 22 37 44 19 32), lower := (rows 11 22 37 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 42 62 44 44 48 32) },{ target := 1, region := (rows 1 0 5 15 16 63), good := (rows 45 60 45 44 48 32) }] }

theorem profile9_node91 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,36] 6 3 profile9_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33,36] 6 3 profile9_node91_cert).mp (by decide +kernel))

def profile9_node85_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node85_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node85 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,33] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node85_route profile9_node85_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node86
  · exact profile9_node87
  · exact profile9_node88
  · exact profile9_node89
  · exact profile9_node90
  · exact profile9_node91

def profile9_node93_cert : CutBound 6 := { lost := (rows 0 1 1 0 2 0), upper := (rows 11 22 38 13 49 32), lower := (rows 11 22 38 13 16 32), losses := [{ target := 0, region := (rows 0 18 23 8 16 63), good := (rows 46 54 38 44 54 32) },{ target := 1, region := (rows 1 0 4 8 25 63), good := (rows 57 52 36 61 48 32) }] }

theorem profile9_node93 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,5] 6 33 profile9_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,5] 6 33 profile9_node93_cert).mp (by decide +kernel))

def profile9_node94_cert : CutBound 6 := { lost := (rows 0 1 1 2 0 0), upper := (rows 11 22 38 41 21 32), lower := (rows 11 22 38 41 16 32), losses := [{ target := 0, region := (rows 0 18 23 8 16 63), good := (rows 46 54 38 44 54 32) },{ target := 1, region := (rows 1 0 4 9 16 63), good := (rows 41 52 36 41 48 32) }] }

theorem profile9_node94 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,33] 6 5 profile9_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,33] 6 5 profile9_node94_cert).mp (by decide +kernel))

def profile9_node95_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 11 22 38 44 17 32), lower := (rows 11 22 38 44 16 32), losses := [{ target := 0, region := (rows 0 18 23 31 16 63), good := (rows 46 62 46 44 62 32) }] }

theorem profile9_node95 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,36] 6 1 profile9_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34,36] 6 1 profile9_node95_cert).mp (by decide +kernel))

def profile9_node92_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node92 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20,34] 6 (by decide) (choices 2) [5,33,36] profile9_node92_route profile9_node92_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node93
  · exact profile9_node94
  · exact profile9_node95

def profile9_node83_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node83_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node83 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,20] 6 (by decide) (choices 2) [3,33,34] profile9_node83_route profile9_node83_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node84
  · exact profile9_node85
  · exact profile9_node92

def profile9_node97_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 11 35 7 60 52 32), lower := (rows 11 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 63), good := (rows 42 34 62 40 48 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 33 61 40 48 32) }] }

theorem profile9_node97 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,3] 6 52 profile9_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,3] 6 52 profile9_node97_cert).mp (by decide +kernel))

def profile9_node99_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 11 35 21 14 52 32), lower := (rows 11 35 21 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 28 63), good := (rows 58 34 52 62 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 61 53 53 60 48 32) }] }

theorem profile9_node99 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,6] 6 36 profile9_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,6] 6 36 profile9_node99_cert).mp (by decide +kernel))

def profile9_node100_cert : CutBound 6 := { lost := (rows 0 0 2 1 3 0), upper := (rows 11 35 21 42 20 32), lower := (rows 11 35 21 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 20 63), good := (rows 42 42 60 42 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 61 53 53 60 48 32) }] }

theorem profile9_node100 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,34] 6 4 profile9_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,34] 6 4 profile9_node100_cert).mp (by decide +kernel))

def profile9_node101_cert : CutBound 6 := { lost := (rows 4 4 0 3 0 0), upper := (rows 11 35 21 44 22 32), lower := (rows 11 35 21 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 63), good := (rows 42 34 60 44 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 41 33 61 44 48 32) },{ target := 2, region := (rows 9 15 0 8 16 63), good := (rows 43 35 51 43 48 32) }] }

theorem profile9_node101 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,36] 6 6 profile9_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17,36] 6 6 profile9_node101_cert).mp (by decide +kernel))

def profile9_node98_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node98_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node98 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,17] 6 (by decide) (choices 2) [6,34,36] profile9_node98_route profile9_node98_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node99
  · exact profile9_node100
  · exact profile9_node101

def profile9_node103_cert : CutBound 6 := { lost := (rows 0 0 1 0 3 0), upper := (rows 11 35 22 13 52 32), lower := (rows 11 35 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 62 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 8 28 63), good := (rows 57 33 52 61 48 32) }] }

theorem profile9_node103 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,5] 6 36 profile9_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,5] 6 36 profile9_node103_cert).mp (by decide +kernel))

def profile9_node104_cert : CutBound 6 := { lost := (rows 0 0 1 2 3 0), upper := (rows 11 35 22 41 20 32), lower := (rows 11 35 22 41 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 62 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 11 20 63), good := (rows 41 41 60 41 48 32) }] }

theorem profile9_node104 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,33] 6 4 profile9_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,33] 6 4 profile9_node104_cert).mp (by decide +kernel))

def profile9_node105_cert : CutBound 6 := { lost := (rows 4 4 0 3 0 0), upper := (rows 11 35 22 44 21 32), lower := (rows 11 35 22 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 63), good := (rows 42 34 62 44 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 41 33 60 44 48 32) },{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 50 43 48 32) }] }

theorem profile9_node105 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,36] 6 5 profile9_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18,36] 6 5 profile9_node105_cert).mp (by decide +kernel))

def profile9_node102_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node102_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node102 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,18] 6 (by decide) (choices 2) [5,33,36] profile9_node102_route profile9_node102_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node103
  · exact profile9_node104
  · exact profile9_node105

def profile9_node106_cert : CutBound 6 := { lost := (rows 4 4 2 0 0 0), upper := (rows 11 35 37 30 22 32), lower := (rows 11 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 45 37 37 40 48 32) },{ target := 2, region := (rows 9 15 0 8 16 63), good := (rows 43 35 35 43 48 32) }] }

theorem profile9_node106 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,33] 6 22 profile9_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,33] 6 22 profile9_node106_cert).mp (by decide +kernel))

def profile9_node107_cert : CutBound 6 := { lost := (rows 4 4 1 0 0 0), upper := (rows 11 35 38 29 21 32), lower := (rows 11 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 46 38 38 40 48 32) },{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 34 43 48 32) }] }

theorem profile9_node107 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,34] 6 21 profile9_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,34] 6 21 profile9_node107_cert).mp (by decide +kernel))

def profile9_node108_cert : CutBound 6 := { lost := (rows 4 4 3 0 0 0), upper := (rows 11 35 52 15 23 32), lower := (rows 11 35 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 20 8 16 63), good := (rows 42 34 52 40 52 32) },{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 41 33 52 40 52 32) },{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 48 43 48 32) }] }

theorem profile9_node108 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,48] 6 7 profile9_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33,48] 6 7 profile9_node108_cert).mp (by decide +kernel))

def profile9_node96_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node96_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node96 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node96_route profile9_node96_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node97
  · exact profile9_node98
  · exact profile9_node102
  · exact profile9_node106
  · exact profile9_node107
  · exact profile9_node108

def profile9_node110_cert : CutBound 6 := { lost := (rows 0 1 0 2 2 0), upper := (rows 11 38 7 61 53 32), lower := (rows 11 38 7 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 42 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 60 61 40 48 32) }] }

theorem profile9_node110 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,3] 6 53 profile9_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,3] 6 53 profile9_node110_cert).mp (by decide +kernel))

def profile9_node112_cert : CutBound 6 := { lost := (rows 0 1 2 0 3 0), upper := (rows 11 38 21 11 52 32), lower := (rows 11 38 21 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 58 54 54 58 48 32) },{ target := 1, region := (rows 1 0 13 8 31 63), good := (rows 61 52 53 61 48 32) }] }

theorem profile9_node112 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,3] 6 36 profile9_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,3] 6 36 profile9_node112_cert).mp (by decide +kernel))

def profile9_node113_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 11 38 21 13 50 32), lower := (rows 11 38 21 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 63), good := (rows 58 54 54 62 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 41 44 61 45 48 32) }] }

theorem profile9_node113 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,5] 6 34 profile9_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,5] 6 34 profile9_node113_cert).mp (by decide +kernel))

def profile9_node114_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 11 38 21 14 49 32), lower := (rows 11 38 21 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 42 46 62 46 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 61 52 53 60 48 32) }] }

theorem profile9_node114 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,6] 6 33 profile9_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,6] 6 33 profile9_node114_cert).mp (by decide +kernel))

def profile9_node115_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 11 38 21 41 22 32), lower := (rows 11 38 21 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 58 54 54 40 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 41 44 61 41 48 32) }] }

theorem profile9_node115 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,33] 6 6 profile9_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,33] 6 6 profile9_node115_cert).mp (by decide +kernel))

def profile9_node116_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 11 38 21 42 21 32), lower := (rows 11 38 21 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 15 16 63), good := (rows 42 46 62 42 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 61 52 53 40 48 32) }] }

theorem profile9_node116 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,34] 6 5 profile9_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,34] 6 5 profile9_node116_cert).mp (by decide +kernel))

def profile9_node117_cert : CutBound 6 := { lost := (rows 0 1 0 3 0 0), upper := (rows 11 38 21 44 19 32), lower := (rows 11 38 21 44 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 42 46 62 46 48 32) },{ target := 1, region := (rows 1 0 4 14 16 63), good := (rows 41 44 61 44 48 32) }] }

theorem profile9_node117 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,36] 6 3 profile9_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17,36] 6 3 profile9_node117_cert).mp (by decide +kernel))

def profile9_node111_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node111_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node111 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,17] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node111_route profile9_node111_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node112
  · exact profile9_node113
  · exact profile9_node114
  · exact profile9_node115
  · exact profile9_node116
  · exact profile9_node117

def profile9_node119_cert : CutBound 6 := { lost := (rows 0 1 1 0 2 0), upper := (rows 11 38 22 13 49 32), lower := (rows 11 38 22 13 16 32), losses := [{ target := 0, region := (rows 0 30 20 8 16 63), good := (rows 42 38 54 46 54 32) },{ target := 1, region := (rows 1 0 4 8 25 63), good := (rows 57 36 52 61 48 32) }] }

theorem profile9_node119 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,5] 6 33 profile9_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,5] 6 33 profile9_node119_cert).mp (by decide +kernel))

def profile9_node120_cert : CutBound 6 := { lost := (rows 0 1 1 2 0 0), upper := (rows 11 38 22 41 21 32), lower := (rows 11 38 22 41 16 32), losses := [{ target := 0, region := (rows 0 22 20 8 16 63), good := (rows 42 38 54 40 54 32) },{ target := 1, region := (rows 1 0 4 9 16 63), good := (rows 41 36 52 41 48 32) }] }

theorem profile9_node120 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,33] 6 5 profile9_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,33] 6 5 profile9_node120_cert).mp (by decide +kernel))

def profile9_node121_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 11 38 22 44 17 32), lower := (rows 11 38 22 44 16 32), losses := [{ target := 0, region := (rows 0 30 20 30 16 63), good := (rows 42 46 62 46 62 32) }] }

theorem profile9_node121 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,36] 6 1 profile9_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18,36] 6 1 profile9_node121_cert).mp (by decide +kernel))

def profile9_node118_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node118_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node118 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,18] 6 (by decide) (choices 2) [5,33,36] profile9_node118_route profile9_node118_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node119
  · exact profile9_node120
  · exact profile9_node121

def profile9_node122_cert : CutBound 6 := { lost := (rows 32 1 2 32 32 0), upper := (rows 11 38 37 31 23 32), lower := (rows 11 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 42 38 38 40 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 45 36 37 40 48 32) },{ target := 5, region := (rows 3 2 4 10 18 0), good := (rows 27 31 5 8 16 0) }] }

theorem profile9_node122 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,33] 6 23 profile9_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,33] 6 23 profile9_node122_cert).mp (by decide +kernel))

def profile9_node123_cert : CutBound 6 := { lost := (rows 32 1 1 32 32 0), upper := (rows 11 38 38 29 21 32), lower := (rows 11 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 46 38 38 46 54 38) },{ target := 5, region := (rows 7 2 4 14 22 0), good := (rows 27 31 31 8 16 0) }] }

theorem profile9_node123 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,34] 6 21 profile9_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,34] 6 21 profile9_node123_cert).mp (by decide +kernel))

def profile9_node124_cert : CutBound 6 := { lost := (rows 0 1 3 0 0 0), upper := (rows 11 38 52 15 23 32), lower := (rows 11 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 22 20 8 16 63), good := (rows 42 38 54 40 54 32) },{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 41 36 52 40 52 32) }] }

theorem profile9_node124 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,48] 6 7 profile9_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36,48] 6 7 profile9_node124_cert).mp (by decide +kernel))

def profile9_node109_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node109_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node109 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,36] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node109_route profile9_node109_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node110
  · exact profile9_node111
  · exact profile9_node118
  · exact profile9_node122
  · exact profile9_node123
  · exact profile9_node124

def profile9_node126_cert : CutBound 6 := { lost := (rows 0 1 0 2 2 0), upper := (rows 11 50 7 45 53 32), lower := (rows 11 50 7 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 42 50 38 40 50 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 48 61 40 48 32) }] }

theorem profile9_node126 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,3] 6 37 profile9_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,3] 6 37 profile9_node126_cert).mp (by decide +kernel))

def profile9_node127_cert : CutBound 6 := { lost := (rows 0 5 2 0 0 0), upper := (rows 11 50 37 15 23 32), lower := (rows 11 50 37 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 42 50 36 40 50 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 45 48 37 40 48 32) },{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 43 50 33 40 50 32) }] }

theorem profile9_node127 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,33] 6 7 profile9_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,33] 6 7 profile9_node127_cert).mp (by decide +kernel))

def profile9_node128_cert : CutBound 6 := { lost := (rows 0 5 1 0 0 0), upper := (rows 11 50 38 13 21 32), lower := (rows 11 50 38 8 16 32), losses := [{ target := 0, region := (rows 0 18 23 8 16 63), good := (rows 46 54 38 40 54 32) },{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 43 50 34 40 50 32) }] }

theorem profile9_node128 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,34] 6 5 profile9_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48,34] 6 5 profile9_node128_cert).mp (by decide +kernel))

def profile9_node125_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node125_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node125 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10,48] 6 (by decide) (choices 2) [3,33,34] profile9_node125_route profile9_node125_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node126
  · exact profile9_node127
  · exact profile9_node128

def profile9_node57_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node57_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node57 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [10] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile9_node57_route profile9_node57_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node58
  · exact profile9_node73
  · exact profile9_node83
  · exact profile9_node96
  · exact profile9_node109
  · exact profile9_node125


#print axioms profile9_node57
end Delivery.SmallBudgetTenFinite6
