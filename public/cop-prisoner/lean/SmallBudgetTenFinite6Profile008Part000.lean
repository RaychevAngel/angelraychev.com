import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile8_node2_cert : CutBound 6 := { lost := (rows 40 40 0 4 4 0), upper := (rows 7 7 47 43 59 32), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) },{ target := 3, region := (rows 7 7 4 0 16 63), good := (rows 39 39 39 32 48 32) },{ target := 5, region := (rows 7 7 4 8 16 0), good := (rows 7 7 7 8 16 0) }] }

theorem profile8_node2 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,5] 6 43 profile8_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,5] 6 43 profile8_node2_cert).mp (by decide +kernel))

def profile8_node4_cert : CutBound 6 := { lost := (rows 8 0 8 3 3 0), upper := (rows 7 11 7 44 60 32), lower := (rows 7 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 63), good := (rows 62 58 62 40 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node4 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,3] 6 44 profile8_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,3] 6 44 profile8_node4_cert).mp (by decide +kernel))

def profile8_node5_cert : CutBound 6 := { lost := (rows 0 4 2 1 9 0), upper := (rows 7 11 13 46 54 32), lower := (rows 7 11 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 6 8 16 63), good := (rows 37 45 45 40 48 32) },{ target := 2, region := (rows 1 6 0 8 16 63), good := (rows 35 43 43 40 48 32) },{ target := 3, region := (rows 1 2 4 0 17 63), good := (rows 55 51 53 32 48 32) }] }

theorem profile8_node5 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,9] 6 38 profile8_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,9] 6 38 profile8_node5_cert).mp (by decide +kernel))

def profile8_node6_cert : CutBound 6 := { lost := (rows 8 0 1 2 10 0), upper := (rows 7 11 14 45 53 32), lower := (rows 7 11 14 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 38 46 46 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 44 40 48 32) },{ target := 3, region := (rows 5 2 4 0 21 63), good := (rows 55 51 55 32 48 32) }] }

theorem profile8_node6 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,10] 6 37 profile8_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,10] 6 37 profile8_node6_cert).mp (by decide +kernel))

def profile8_node7_cert : CutBound 6 := { lost := (rows 8 0 10 1 1 0), upper := (rows 7 11 37 46 62 32), lower := (rows 7 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 45 37 40 48 32) },{ target := 3, region := (rows 3 2 7 0 16 63), good := (rows 39 39 37 32 48 32) }] }

theorem profile8_node7 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,33] 6 46 profile8_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,33] 6 46 profile8_node7_cert).mp (by decide +kernel))

def profile8_node8_cert : CutBound 6 := { lost := (rows 8 0 9 2 2 0), upper := (rows 7 11 38 45 61 32), lower := (rows 7 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 46 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node8 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,34] 6 45 profile8_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,34] 6 45 profile8_node8_cert).mp (by decide +kernel))

def profile8_node9_cert : CutBound 6 := { lost := (rows 32 32 3 0 8 0), upper := (rows 7 11 44 47 55 32), lower := (rows 7 11 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 16 63), good := (rows 38 46 44 44 48 32) },{ target := 1, region := (rows 1 0 14 8 16 63), good := (rows 37 45 44 44 48 32) },{ target := 3, region := (rows 1 2 4 0 17 63), good := (rows 55 51 36 32 48 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 7 11 15 8 16 0) }] }

theorem profile8_node9 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,40] 6 39 profile8_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9,40] 6 39 profile8_node9_cert).mp (by decide +kernel))

def profile8_node3_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node3 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,9] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node3_route profile8_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node4
  · exact profile8_node5
  · exact profile8_node6
  · exact profile8_node7
  · exact profile8_node8
  · exact profile8_node9

def profile8_node11_cert : CutBound 6 := { lost := (rows 8 0 8 6 6 0), upper := (rows 7 14 7 41 57 32), lower := (rows 7 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 60 61 40 48 32) },{ target := 2, region := (rows 1 2 0 13 21 63), good := (rows 59 58 59 40 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node11 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,3] 6 41 profile8_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,3] 6 41 profile8_node11_cert).mp (by decide +kernel))

def profile8_node12_cert : CutBound 6 := { lost := (rows 8 1 0 4 12 0), upper := (rows 7 14 13 43 51 32), lower := (rows 7 14 13 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 38 46 46 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 57 40 48 32) },{ target := 3, region := (rows 3 2 4 0 19 63), good := (rows 55 55 53 32 48 32) }] }

theorem profile8_node12 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,9] 6 35 profile8_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,9] 6 35 profile8_node12_cert).mp (by decide +kernel))

def profile8_node13_cert : CutBound 6 := { lost := (rows 0 1 1 6 6 0), upper := (rows 7 14 14 41 49 32), lower := (rows 7 14 14 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 44 44 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 42 40 48 32) }] }

theorem profile8_node13 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,10] 6 33 profile8_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,10] 6 33 profile8_node13_cert).mp (by decide +kernel))

def profile8_node14_cert : CutBound 6 := { lost := (rows 8 0 10 4 4 0), upper := (rows 7 14 37 43 59 32), lower := (rows 7 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 44 37 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 57 40 48 32) },{ target := 3, region := (rows 3 2 7 0 16 63), good := (rows 39 39 37 32 48 32) }] }

theorem profile8_node14 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,33] 6 43 profile8_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,33] 6 43 profile8_node14_cert).mp (by decide +kernel))

def profile8_node15_cert : CutBound 6 := { lost := (rows 0 1 1 6 6 0), upper := (rows 7 14 38 41 57 32), lower := (rows 7 14 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 44 36 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 34 40 48 32) }] }

theorem profile8_node15 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,34] 6 41 profile8_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,34] 6 41 profile8_node15_cert).mp (by decide +kernel))

def profile8_node16_cert : CutBound 6 := { lost := (rows 0 1 3 4 4 0), upper := (rows 7 14 44 43 51 32), lower := (rows 7 14 44 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 1, region := (rows 1 0 14 8 16 63), good := (rows 37 44 44 44 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 40 40 48 32) }] }

theorem profile8_node16 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,40] 6 35 profile8_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12,40] 6 35 profile8_node16_cert).mp (by decide +kernel))

def profile8_node10_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node10 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,12] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node10_route profile8_node10_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node11
  · exact profile8_node12
  · exact profile8_node13
  · exact profile8_node14
  · exact profile8_node15
  · exact profile8_node16

def profile8_node18_cert : CutBound 6 := { lost := (rows 0 4 0 3 3 0), upper := (rows 7 35 7 44 60 32), lower := (rows 7 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 63), good := (rows 62 58 62 40 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 35 35 35 40 48 32) }] }

theorem profile8_node18 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,3] 6 44 profile8_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,3] 6 44 profile8_node18_cert).mp (by decide +kernel))

def profile8_node19_cert : CutBound 6 := { lost := (rows 8 12 0 1 1 0), upper := (rows 7 35 13 46 62 32), lower := (rows 7 35 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 35 35 43 40 48 32) },{ target := 3, region := (rows 5 7 4 0 16 63), good := (rows 39 35 39 32 48 32) }] }

theorem profile8_node19 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,9] 6 46 profile8_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,9] 6 46 profile8_node19_cert).mp (by decide +kernel))

def profile8_node20_cert : CutBound 6 := { lost := (rows 8 12 0 2 2 0), upper := (rows 7 35 14 45 61 32), lower := (rows 7 35 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 44 40 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 42 40 48 32) },{ target := 3, region := (rows 5 7 4 0 16 63), good := (rows 39 35 39 32 48 32) }] }

theorem profile8_node20 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,10] 6 45 profile8_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,10] 6 45 profile8_node20_cert).mp (by decide +kernel))

def profile8_node21_cert : CutBound 6 := { lost := (rows 8 12 10 1 1 0), upper := (rows 7 35 37 14 30 32), lower := (rows 7 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 35 35 35 40 48 32) },{ target := 3, region := (rows 63 63 63 0 16 63), good := (rows 39 39 39 39 55 39) }] }

theorem profile8_node21 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,33] 6 14 profile8_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,33] 6 14 profile8_node21_cert).mp (by decide +kernel))

def profile8_node22_cert : CutBound 6 := { lost := (rows 8 12 9 2 2 0), upper := (rows 7 35 38 13 29 32), lower := (rows 7 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 34 40 48 32) },{ target := 3, region := (rows 63 63 63 0 16 63), good := (rows 39 39 39 39 55 39) }] }

theorem profile8_node22 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,34] 6 13 profile8_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,34] 6 13 profile8_node22_cert).mp (by decide +kernel))

def profile8_node23_cert : CutBound 6 := { lost := (rows 8 12 3 0 0 0), upper := (rows 7 35 44 15 31 32), lower := (rows 7 35 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 38 34 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 37 33 44 44 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 40 40 48 32) },{ target := 3, region := (rows 5 7 4 0 16 63), good := (rows 39 35 39 32 48 32) }] }

theorem profile8_node23 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,40] 6 15 profile8_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33,40] 6 15 profile8_node23_cert).mp (by decide +kernel))

def profile8_node17_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node17 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,33] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node17_route profile8_node17_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node18
  · exact profile8_node19
  · exact profile8_node20
  · exact profile8_node21
  · exact profile8_node22
  · exact profile8_node23

def profile8_node24_cert : CutBound 6 := { lost := (rows 8 9 0 4 4 0), upper := (rows 7 38 47 43 59 32), lower := (rows 7 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) },{ target := 3, region := (rows 7 7 4 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node24 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,36] 6 43 profile8_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,36] 6 43 profile8_node24_cert).mp (by decide +kernel))

def profile8_node26_cert : CutBound 6 := { lost := (rows 8 5 8 2 2 0), upper := (rows 7 42 7 45 61 32), lower := (rows 7 42 7 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 38 42 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 40 61 40 48 32) },{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 35 42 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node26 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,3] 6 45 profile8_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,3] 6 45 profile8_node26_cert).mp (by decide +kernel))

def profile8_node27_cert : CutBound 6 := { lost := (rows 32 5 32 0 8 0), upper := (rows 7 42 13 47 55 32), lower := (rows 7 42 13 8 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 16 63), good := (rows 38 42 46 42 48 32) },{ target := 2, region := (rows 1 14 0 8 16 63), good := (rows 35 42 43 42 48 32) },{ target := 3, region := (rows 1 2 4 0 17 63), good := (rows 55 34 53 32 48 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 7 15 13 8 16 0) }] }

theorem profile8_node27 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,9] 6 39 profile8_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,9] 6 39 profile8_node27_cert).mp (by decide +kernel))

def profile8_node28_cert : CutBound 6 := { lost := (rows 0 5 1 2 2 0), upper := (rows 7 42 14 45 53 32), lower := (rows 7 42 14 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 40 44 40 48 32) },{ target := 2, region := (rows 1 14 0 8 16 63), good := (rows 35 42 42 42 48 32) }] }

theorem profile8_node28 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,10] 6 37 profile8_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,10] 6 37 profile8_node28_cert).mp (by decide +kernel))

def profile8_node29_cert : CutBound 6 := { lost := (rows 8 5 10 0 0 0), upper := (rows 7 42 37 15 31 32), lower := (rows 7 42 37 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 36 42 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 40 37 40 48 32) },{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 33 42 48 32) },{ target := 3, region := (rows 3 2 7 0 16 63), good := (rows 39 39 37 32 48 32) }] }

theorem profile8_node29 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,33] 6 15 profile8_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,33] 6 15 profile8_node29_cert).mp (by decide +kernel))

def profile8_node30_cert : CutBound 6 := { lost := (rows 0 5 1 2 2 0), upper := (rows 7 42 38 13 29 32), lower := (rows 7 42 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 40 36 40 48 32) },{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 34 42 48 32) }] }

theorem profile8_node30 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,34] 6 13 profile8_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,34] 6 13 profile8_node30_cert).mp (by decide +kernel))

def profile8_node31_cert : CutBound 6 := { lost := (rows 0 5 3 0 8 0), upper := (rows 7 42 44 15 23 32), lower := (rows 7 42 44 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 1, region := (rows 1 0 14 8 16 63), good := (rows 37 44 44 44 48 32) },{ target := 2, region := (rows 1 14 0 8 16 63), good := (rows 35 42 42 42 48 32) },{ target := 3, region := (rows 1 2 4 0 17 63), good := (rows 55 34 36 32 48 32) }] }

theorem profile8_node31 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,40] 6 7 profile8_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40,40] 6 7 profile8_node31_cert).mp (by decide +kernel))

def profile8_node25_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node25_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node25 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6,40] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node25_route profile8_node25_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node26
  · exact profile8_node27
  · exact profile8_node28
  · exact profile8_node29
  · exact profile8_node30
  · exact profile8_node31

def profile8_node1_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [6] 6 (by decide) (choices 2) [5,9,12,33,36,40] profile8_node1_route profile8_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node2
  · exact profile8_node3
  · exact profile8_node10
  · exact profile8_node17
  · exact profile8_node24
  · exact profile8_node25

def profile8_node34_cert : CutBound 6 := { lost := (rows 4 0 0 3 3 0), upper := (rows 35 7 7 44 60 32), lower := (rows 35 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 58 62 62 40 48 32) },{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 35 35 40 48 32) }] }

theorem profile8_node34 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,3] 6 44 profile8_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,3] 6 44 profile8_node34_cert).mp (by decide +kernel))

def profile8_node35_cert : CutBound 6 := { lost := (rows 12 8 0 1 1 0), upper := (rows 35 7 13 46 62 32), lower := (rows 35 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 44 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 41 40 48 32) },{ target := 3, region := (rows 7 6 4 0 16 63), good := (rows 35 39 39 32 48 32) }] }

theorem profile8_node35 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,9] 6 46 profile8_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,9] 6 46 profile8_node35_cert).mp (by decide +kernel))

def profile8_node36_cert : CutBound 6 := { lost := (rows 12 8 0 2 2 0), upper := (rows 35 7 14 45 61 32), lower := (rows 35 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 35 43 40 48 32) },{ target := 3, region := (rows 7 6 4 0 16 63), good := (rows 35 39 39 32 48 32) }] }

theorem profile8_node36 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,10] 6 45 profile8_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,10] 6 45 profile8_node36_cert).mp (by decide +kernel))

def profile8_node37_cert : CutBound 6 := { lost := (rows 12 8 10 1 1 0), upper := (rows 35 7 37 14 30 32), lower := (rows 35 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 36 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 33 40 48 32) },{ target := 3, region := (rows 63 63 63 0 16 63), good := (rows 39 39 39 39 55 39) }] }

theorem profile8_node37 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,33] 6 14 profile8_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,33] 6 14 profile8_node37_cert).mp (by decide +kernel))

def profile8_node38_cert : CutBound 6 := { lost := (rows 12 8 9 2 2 0), upper := (rows 35 7 38 13 29 32), lower := (rows 35 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 35 35 40 48 32) },{ target := 3, region := (rows 63 63 63 0 16 63), good := (rows 39 39 39 39 55 39) }] }

theorem profile8_node38 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,34] 6 13 profile8_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,34] 6 13 profile8_node38_cert).mp (by decide +kernel))

def profile8_node39_cert : CutBound 6 := { lost := (rows 12 8 3 0 0 0), upper := (rows 35 7 44 15 31 32), lower := (rows 35 7 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 34 38 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 33 37 44 44 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 40 40 48 32) },{ target := 3, region := (rows 7 6 4 0 16 63), good := (rows 35 39 39 32 48 32) }] }

theorem profile8_node39 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,40] 6 15 profile8_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5,40] 6 15 profile8_node39_cert).mp (by decide +kernel))

def profile8_node33_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node33_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node33 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,5] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node33_route profile8_node33_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node34
  · exact profile8_node35
  · exact profile8_node36
  · exact profile8_node37
  · exact profile8_node38
  · exact profile8_node39

def profile8_node41_cert : CutBound 6 := { lost := (rows 12 0 8 2 2 0), upper := (rows 35 14 7 45 61 32), lower := (rows 35 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 33 60 61 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 43 35 40 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node41 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,3] 6 45 profile8_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,3] 6 45 profile8_node41_cert).mp (by decide +kernel))

def profile8_node42_cert : CutBound 6 := { lost := (rows 12 33 0 0 8 0), upper := (rows 35 14 13 47 55 32), lower := (rows 35 14 13 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 34 46 46 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 41 40 48 32) },{ target := 3, region := (rows 3 2 4 0 18 63), good := (rows 51 55 37 32 48 32) },{ target := 5, region := (rows 1 6 4 8 16 0), good := (rows 3 14 15 8 16 0) }] }

theorem profile8_node42 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,9] 6 39 profile8_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,9] 6 39 profile8_node42_cert).mp (by decide +kernel))

def profile8_node43_cert : CutBound 6 := { lost := (rows 12 1 1 0 8 0), upper := (rows 35 14 14 45 53 32), lower := (rows 35 14 14 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 43 43 40 48 32) },{ target := 3, region := (rows 7 2 4 0 22 63), good := (rows 51 55 55 32 48 32) }] }

theorem profile8_node43 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,10] 6 37 profile8_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,10] 6 37 profile8_node43_cert).mp (by decide +kernel))

def profile8_node44_cert : CutBound 6 := { lost := (rows 12 32 10 32 32 0), upper := (rows 35 14 37 15 31 32), lower := (rows 35 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 44 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 33 40 48 32) },{ target := 3, region := (rows 3 2 7 0 16 63), good := (rows 39 39 37 32 48 32) },{ target := 5, region := (rows 1 6 4 12 20 0), good := (rows 3 30 31 8 16 0) }] }

theorem profile8_node44 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,33] 6 15 profile8_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,33] 6 15 profile8_node44_cert).mp (by decide +kernel))

def profile8_node45_cert : CutBound 6 := { lost := (rows 12 1 9 0 0 0), upper := (rows 35 14 38 13 29 32), lower := (rows 35 14 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 43 35 40 48 32) },{ target := 3, region := (rows 7 2 7 0 16 63), good := (rows 39 39 39 32 48 32) }] }

theorem profile8_node45 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,34] 6 13 profile8_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,34] 6 13 profile8_node45_cert).mp (by decide +kernel))

def profile8_node46_cert : CutBound 6 := { lost := (rows 12 1 3 0 8 0), upper := (rows 35 14 44 15 23 32), lower := (rows 35 14 44 8 16 32), losses := [{ target := 0, region := (rows 0 14 14 8 16 63), good := (rows 38 46 46 46 48 32) },{ target := 1, region := (rows 1 0 14 8 16 63), good := (rows 37 44 44 44 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 40 40 48 32) },{ target := 3, region := (rows 3 2 4 0 18 63), good := (rows 51 55 36 32 48 32) }] }

theorem profile8_node46 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,40] 6 7 profile8_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12,40] 6 7 profile8_node46_cert).mp (by decide +kernel))

def profile8_node40_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile8_node40 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,12] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile8_node40_route profile8_node40_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node41
  · exact profile8_node42
  · exact profile8_node43
  · exact profile8_node44
  · exact profile8_node45
  · exact profile8_node46

def profile8_node47_cert : CutBound 6 := { lost := (rows 12 12 32 32 32 0), upper := (rows 35 35 15 15 31 32), lower := (rows 35 35 4 8 16 32), losses := [{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) },{ target := 3, region := (rows 63 63 4 0 16 63), good := (rows 35 35 39 35 51 35) },{ target := 5, region := (rows 1 2 7 11 19 0), good := (rows 31 31 4 8 16 0) }] }

theorem profile8_node47 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,33] 6 15 profile8_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,33] 6 15 profile8_node47_cert).mp (by decide +kernel))

def profile8_node48_cert : CutBound 6 := { lost := (rows 12 9 32 32 32 0), upper := (rows 35 38 15 15 31 32), lower := (rows 35 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 34 38 38 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 32 40 48 32) },{ target := 3, region := (rows 7 6 4 0 16 63), good := (rows 35 39 39 32 48 32) },{ target := 5, region := (rows 1 2 5 9 17 0), good := (rows 31 6 4 8 16 0) }] }

theorem profile8_node48 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,36] 6 15 profile8_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34,36] 6 15 profile8_node48_cert).mp (by decide +kernel))

def profile8_node32_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node32_route : Route 6 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile8_node32 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [34] 6 (by decide) (choices 2) [5,12,33,36] profile8_node32_route profile8_node32_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node33
  · exact profile8_node40
  · exact profile8_node47
  · exact profile8_node48

def profile8_node0_column : Nat → Fin 6 := fun mask => match mask with | 18 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile8_node0_route : Route 6 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile8_node0 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [] 6 (by decide) (choices 2) [6,34] profile8_node0_route profile8_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node1
  · exact profile8_node32

theorem profile8 : Upper (D (n:=6) [34,34,34,34,32,2]) (R (n:=6) [34,34,34,34,32,2]) [] 6 := profile8_node0


#print axioms profile8
end Delivery.SmallBudgetTenFinite6
