import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 7 7 63 59 59 59), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 35), good := (rows 59 59 0 8 16 32) }] }

theorem profile10_node2 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,5] 6 59 profile10_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,5] 6 59 profile10_node2_cert).mp (by decide +kernel))

def profile10_node4_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 11 7 60 52 52), lower := (rows 7 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 37), good := (rows 62 58 62 8 16 32) }] }

theorem profile10_node4 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,3] 6 52 profile10_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,3] 6 52 profile10_node4_cert).mp (by decide +kernel))

def profile10_node5_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 11 21 62 54 54), lower := (rows 7 11 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node5 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,17] 6 54 profile10_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,17] 6 54 profile10_node5_cert).mp (by decide +kernel))

def profile10_node6_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 11 22 61 53 53), lower := (rows 7 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 20 8 16 32) }] }

theorem profile10_node6 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,18] 6 53 profile10_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,18] 6 53 profile10_node6_cert).mp (by decide +kernel))

def profile10_node7_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 11 37 30 22 54), lower := (rows 7 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node7 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,33] 6 22 profile10_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,33] 6 22 profile10_node7_cert).mp (by decide +kernel))

def profile10_node8_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 11 38 29 21 53), lower := (rows 7 11 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 36 8 16 32) }] }

theorem profile10_node8 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,34] 6 21 profile10_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,34] 6 21 profile10_node8_cert).mp (by decide +kernel))

def profile10_node10_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 11 52 11 20 52), lower := (rows 7 11 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 62 52 62 52 52) }] }

theorem profile10_node10 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,3] 6 20 profile10_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,3] 6 20 profile10_node10_cert).mp (by decide +kernel))

def profile10_node11_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 11 52 13 18 50), lower := (rows 7 11 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 62 52 60 16 32) }] }

theorem profile10_node11 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,5] 6 18 profile10_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,5] 6 18 profile10_node11_cert).mp (by decide +kernel))

def profile10_node12_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 11 52 14 17 49), lower := (rows 7 11 52 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 10 52 14 16 32) }] }

theorem profile10_node12 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,6] 6 17 profile10_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,6] 6 17 profile10_node12_cert).mp (by decide +kernel))

def profile10_node13_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 11 52 25 22 38), lower := (rows 7 11 52 25 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 62 52 60 16 32) }] }

theorem profile10_node13 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,17] 6 6 profile10_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,17] 6 6 profile10_node13_cert).mp (by decide +kernel))

def profile10_node14_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 7 11 52 26 21 37), lower := (rows 7 11 52 26 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 61 52 60 16 32) }] }

theorem profile10_node14 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,18] 6 5 profile10_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,18] 6 5 profile10_node14_cert).mp (by decide +kernel))

def profile10_node15_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 11 52 28 19 35), lower := (rows 7 11 52 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 14 10 60 28 16 32) }] }

theorem profile10_node15 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,20] 6 3 profile10_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48,20] 6 3 profile10_node15_cert).mp (by decide +kernel))

def profile10_node9_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node9 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9,48] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node9_route profile10_node9_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node10
  · exact profile10_node11
  · exact profile10_node12
  · exact profile10_node13
  · exact profile10_node14
  · exact profile10_node15

def profile10_node3_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node3 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node3_route profile10_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node4
  · exact profile10_node5
  · exact profile10_node6
  · exact profile10_node7
  · exact profile10_node8
  · exact profile10_node9

def profile10_node16_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 7 14 55 59 51 51), lower := (rows 7 14 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 33), good := (rows 59 10 0 8 16 32) }] }

theorem profile10_node16 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,12] 6 51 profile10_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,12] 6 51 profile10_node16_cert).mp (by decide +kernel))

def profile10_node18_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 7 60 60 60), lower := (rows 7 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 37), good := (rows 62 58 62 8 16 32) }] }

theorem profile10_node18 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,3] 6 60 profile10_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,3] 6 60 profile10_node18_cert).mp (by decide +kernel))

def profile10_node19_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 13 62 54 54), lower := (rows 7 19 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node19 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,9] 6 54 profile10_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,9] 6 54 profile10_node19_cert).mp (by decide +kernel))

def profile10_node20_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 14 61 53 53), lower := (rows 7 19 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 12 8 16 32) }] }

theorem profile10_node20 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,10] 6 53 profile10_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,10] 6 53 profile10_node20_cert).mp (by decide +kernel))

def profile10_node21_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 21 46 62 46), lower := (rows 7 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node21 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,17] 6 46 profile10_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,17] 6 46 profile10_node21_cert).mp (by decide +kernel))

def profile10_node22_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 22 45 61 45), lower := (rows 7 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 22 22 8 16 32) }] }

theorem profile10_node22 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,18] 6 45 profile10_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,18] 6 45 profile10_node22_cert).mp (by decide +kernel))

def profile10_node23_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 19 28 47 55 39), lower := (rows 7 19 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 43 12 8 0 32) }] }

theorem profile10_node23 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,24] 6 39 profile10_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,24] 6 39 profile10_node23_cert).mp (by decide +kernel))

def profile10_node24_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 37 30 30 62), lower := (rows 7 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node24 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,33] 6 30 profile10_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,33] 6 30 profile10_node24_cert).mp (by decide +kernel))

def profile10_node25_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 38 29 29 61), lower := (rows 7 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 36 8 16 32) }] }

theorem profile10_node25 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,34] 6 29 profile10_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,34] 6 29 profile10_node25_cert).mp (by decide +kernel))

def profile10_node27_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 44 11 20 52), lower := (rows 7 19 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 29 45), good := (rows 54 50 60 62 16 32) }] }

theorem profile10_node27 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,3] 6 20 profile10_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,3] 6 20 profile10_node27_cert).mp (by decide +kernel))

def profile10_node28_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 44 13 18 50), lower := (rows 7 19 44 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 54 50 44 60 16 32) }] }

theorem profile10_node28 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,5] 6 18 profile10_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,5] 6 18 profile10_node28_cert).mp (by decide +kernel))

def profile10_node29_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 44 14 17 49), lower := (rows 7 19 44 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 26 44 14 16 32) }] }

theorem profile10_node29 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,6] 6 17 profile10_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,6] 6 17 profile10_node29_cert).mp (by decide +kernel))

def profile10_node30_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 44 25 22 38), lower := (rows 7 19 44 25 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 17 33), good := (rows 54 50 44 60 16 32) }] }

theorem profile10_node30 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,17] 6 6 profile10_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,17] 6 6 profile10_node30_cert).mp (by decide +kernel))

def profile10_node31_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 44 26 21 37), lower := (rows 7 19 44 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 14 26 44 26 16 32) }] }

theorem profile10_node31 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,18] 6 5 profile10_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,18] 6 5 profile10_node31_cert).mp (by decide +kernel))

def profile10_node32_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 7 19 44 28 19 35), lower := (rows 7 19 44 28 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 19 35), good := (rows 51 51 40 24 16 32) }] }

theorem profile10_node32 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,20] 6 3 profile10_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40,20] 6 3 profile10_node32_cert).mp (by decide +kernel))

def profile10_node26_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node26_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node26 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,40] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node26_route profile10_node26_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node27
  · exact profile10_node28
  · exact profile10_node29
  · exact profile10_node30
  · exact profile10_node31
  · exact profile10_node32

def profile10_node33_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 19 52 15 31 47), lower := (rows 7 19 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 43 36 8 0 32) }] }

theorem profile10_node33 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,48] 6 15 profile10_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17,48] 6 15 profile10_node33_cert).mp (by decide +kernel))

def profile10_node17_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile10_node17_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node17 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,17] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile10_node17_route profile10_node17_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node18
  · exact profile10_node19
  · exact profile10_node20
  · exact profile10_node21
  · exact profile10_node22
  · exact profile10_node23
  · exact profile10_node24
  · exact profile10_node25
  · exact profile10_node26
  · exact profile10_node33

def profile10_node34_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 7 22 63 59 59 59), lower := (rows 7 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 33), good := (rows 59 18 0 8 16 32) }] }

theorem profile10_node34 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,20] 6 59 profile10_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,20] 6 59 profile10_node34_cert).mp (by decide +kernel))

def profile10_node36_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 26 7 61 53 53), lower := (rows 7 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 24 61 8 16 32) }] }

theorem profile10_node36 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,3] 6 53 profile10_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,3] 6 53 profile10_node36_cert).mp (by decide +kernel))

def profile10_node37_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 26 21 47 55 39), lower := (rows 7 26 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 10 45 8 0 32) }] }

theorem profile10_node37 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,17] 6 39 profile10_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,17] 6 39 profile10_node37_cert).mp (by decide +kernel))

def profile10_node38_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 26 22 45 53 37), lower := (rows 7 26 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 30 22 8 16 32) }] }

theorem profile10_node38 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,18] 6 37 profile10_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,18] 6 37 profile10_node38_cert).mp (by decide +kernel))

def profile10_node40_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 26 37 11 20 52), lower := (rows 7 26 37 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 21 37), good := (rows 54 26 52 58 16 32) }] }

theorem profile10_node40 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,3] 6 20 profile10_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,3] 6 20 profile10_node40_cert).mp (by decide +kernel))

def profile10_node41_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 26 37 13 18 50), lower := (rows 7 26 37 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 54 58 52 62 16 32) }] }

theorem profile10_node41 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,5] 6 18 profile10_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,5] 6 18 profile10_node41_cert).mp (by decide +kernel))

def profile10_node42_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 26 37 14 17 49), lower := (rows 7 26 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 26 44 14 16 32) }] }

theorem profile10_node42 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,6] 6 17 profile10_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,6] 6 17 profile10_node42_cert).mp (by decide +kernel))

def profile10_node43_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 26 37 25 22 38), lower := (rows 7 26 37 25 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 17 33), good := (rows 54 26 52 58 16 32) }] }

theorem profile10_node43 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,17] 6 6 profile10_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,17] 6 6 profile10_node43_cert).mp (by decide +kernel))

def profile10_node44_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 7 26 37 26 21 37), lower := (rows 7 26 37 26 16 32), losses := [{ target := 0, region := (rows 0 26 4 26 16 32), good := (rows 14 26 36 26 26 32) }] }

theorem profile10_node44 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,18] 6 5 profile10_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,18] 6 5 profile10_node44_cert).mp (by decide +kernel))

def profile10_node45_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 26 37 28 19 35), lower := (rows 7 26 37 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 6 26 36 30 16 32) }] }

theorem profile10_node45 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,20] 6 3 profile10_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33,20] 6 3 profile10_node45_cert).mp (by decide +kernel))

def profile10_node39_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node39 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,33] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node39_route profile10_node39_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node40
  · exact profile10_node41
  · exact profile10_node42
  · exact profile10_node43
  · exact profile10_node44
  · exact profile10_node45

def profile10_node46_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 26 38 29 21 53), lower := (rows 7 26 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 24 36 8 16 32) }] }

theorem profile10_node46 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,34] 6 21 profile10_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,34] 6 21 profile10_node46_cert).mp (by decide +kernel))

def profile10_node47_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 26 52 15 23 39), lower := (rows 7 26 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 10 36 8 0 32) }] }

theorem profile10_node47 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,48] 6 7 profile10_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24,48] 6 7 profile10_node47_cert).mp (by decide +kernel))

def profile10_node35_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node35 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,24] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node35_route profile10_node35_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node36
  · exact profile10_node37
  · exact profile10_node38
  · exact profile10_node39
  · exact profile10_node46
  · exact profile10_node47

def profile10_node49_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 35 7 28 28 60), lower := (rows 7 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 37), good := (rows 62 58 62 8 16 32) }] }

theorem profile10_node49 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,3] 6 28 profile10_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,3] 6 28 profile10_node49_cert).mp (by decide +kernel))

def profile10_node50_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 35 13 30 22 54), lower := (rows 7 35 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node50 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,9] 6 22 profile10_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,9] 6 22 profile10_node50_cert).mp (by decide +kernel))

def profile10_node51_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 35 14 29 21 53), lower := (rows 7 35 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 12 8 16 32) }] }

theorem profile10_node51 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,10] 6 21 profile10_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,10] 6 21 profile10_node51_cert).mp (by decide +kernel))

def profile10_node52_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 35 21 30 30 62), lower := (rows 7 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) }] }

theorem profile10_node52 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,17] 6 30 profile10_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,17] 6 30 profile10_node52_cert).mp (by decide +kernel))

def profile10_node53_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 35 22 29 29 61), lower := (rows 7 35 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 20 8 16 32) }] }

theorem profile10_node53 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,18] 6 29 profile10_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,18] 6 29 profile10_node53_cert).mp (by decide +kernel))

def profile10_node55_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 35 28 11 20 52), lower := (rows 7 35 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 29 45), good := (rows 54 50 60 62 16 32) }] }

theorem profile10_node55 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,3] 6 20 profile10_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,3] 6 20 profile10_node55_cert).mp (by decide +kernel))

def profile10_node56_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 35 28 13 18 50), lower := (rows 7 35 28 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 54 50 28 60 16 32) }] }

theorem profile10_node56 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,5] 6 18 profile10_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,5] 6 18 profile10_node56_cert).mp (by decide +kernel))

def profile10_node57_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 35 28 14 17 49), lower := (rows 7 35 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 42 28 14 16 32) }] }

theorem profile10_node57 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,6] 6 17 profile10_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,6] 6 17 profile10_node57_cert).mp (by decide +kernel))

def profile10_node58_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 35 28 25 22 38), lower := (rows 7 35 28 25 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 17 33), good := (rows 54 50 28 60 16 32) }] }

theorem profile10_node58 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,17] 6 6 profile10_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,17] 6 6 profile10_node58_cert).mp (by decide +kernel))

def profile10_node59_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 35 28 26 21 37), lower := (rows 7 35 28 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 6 34 28 30 16 32) }] }

theorem profile10_node59 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,18] 6 5 profile10_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,18] 6 5 profile10_node59_cert).mp (by decide +kernel))

def profile10_node60_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 7 35 28 28 19 35), lower := (rows 7 35 28 28 16 32), losses := [{ target := 0, region := (rows 0 2 28 28 16 32), good := (rows 14 34 28 28 28 32) }] }

theorem profile10_node60 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,20] 6 3 profile10_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24,20] 6 3 profile10_node60_cert).mp (by decide +kernel))

def profile10_node54_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node54_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node54 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33,24] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node54_route profile10_node54_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node55
  · exact profile10_node56
  · exact profile10_node57
  · exact profile10_node58
  · exact profile10_node59
  · exact profile10_node60

def profile10_node48_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node48 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,33] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node48_route profile10_node48_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node49
  · exact profile10_node50
  · exact profile10_node51
  · exact profile10_node52
  · exact profile10_node53
  · exact profile10_node54

def profile10_node61_cert : CutBound 6 := { lost := (rows 0 0 0 4 0 0), upper := (rows 7 38 31 27 27 59), lower := (rows 7 38 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 33), good := (rows 59 34 0 8 16 32) }] }

theorem profile10_node61 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,36] 6 27 profile10_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,36] 6 27 profile10_node61_cert).mp (by decide +kernel))

def profile10_node63_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 42 7 29 21 53), lower := (rows 7 42 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 40 61 8 16 32) }] }

theorem profile10_node63 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,3] 6 21 profile10_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,3] 6 21 profile10_node63_cert).mp (by decide +kernel))

def profile10_node65_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 42 21 11 20 52), lower := (rows 7 42 21 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 21 37), good := (rows 54 42 52 58 16 32) }] }

theorem profile10_node65 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,3] 6 20 profile10_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,3] 6 20 profile10_node65_cert).mp (by decide +kernel))

def profile10_node66_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 42 21 13 18 50), lower := (rows 7 42 21 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 54 58 52 62 16 32) }] }

theorem profile10_node66 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,5] 6 18 profile10_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,5] 6 18 profile10_node66_cert).mp (by decide +kernel))

def profile10_node67_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 42 21 14 17 49), lower := (rows 7 42 21 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 42 28 14 16 32) }] }

theorem profile10_node67 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,6] 6 17 profile10_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,6] 6 17 profile10_node67_cert).mp (by decide +kernel))

def profile10_node68_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 42 21 25 22 38), lower := (rows 7 42 21 25 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 17 33), good := (rows 54 42 52 58 16 32) }] }

theorem profile10_node68 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,17] 6 6 profile10_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,17] 6 6 profile10_node68_cert).mp (by decide +kernel))

def profile10_node69_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 7 42 21 26 21 37), lower := (rows 7 42 21 26 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 21 37), good := (rows 53 40 53 24 16 32) }] }

theorem profile10_node69 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,18] 6 5 profile10_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,18] 6 5 profile10_node69_cert).mp (by decide +kernel))

def profile10_node70_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 42 21 28 19 35), lower := (rows 7 42 21 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 14 42 28 28 16 32) }] }

theorem profile10_node70 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,20] 6 3 profile10_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17,20] 6 3 profile10_node70_cert).mp (by decide +kernel))

def profile10_node64_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node64_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node64 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,17] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node64_route profile10_node64_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node65
  · exact profile10_node66
  · exact profile10_node67
  · exact profile10_node68
  · exact profile10_node69
  · exact profile10_node70

def profile10_node71_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 42 22 29 21 53), lower := (rows 7 42 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 40 20 8 16 32) }] }

theorem profile10_node71 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,18] 6 21 profile10_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40,18] 6 21 profile10_node71_cert).mp (by decide +kernel))

def profile10_node62_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node62_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node62 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,40] 6 (by decide) (choices 2) [3,17,18] profile10_node62_route profile10_node62_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node63
  · exact profile10_node64
  · exact profile10_node71

def profile10_node73_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 50 7 29 29 61), lower := (rows 7 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 48 61 8 16 32) }] }

theorem profile10_node73 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,3] 6 29 profile10_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,3] 6 29 profile10_node73_cert).mp (by decide +kernel))

def profile10_node75_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 50 13 11 20 52), lower := (rows 7 50 13 11 16 32), losses := [{ target := 0, region := (rows 0 15 4 8 21 37), good := (rows 54 50 62 58 16 32) }] }

theorem profile10_node75 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,3] 6 20 profile10_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,3] 6 20 profile10_node75_cert).mp (by decide +kernel))

def profile10_node76_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 50 13 13 18 50), lower := (rows 7 50 13 13 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 62 62 50 50) }] }

theorem profile10_node76 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,5] 6 18 profile10_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,5] 6 18 profile10_node76_cert).mp (by decide +kernel))

def profile10_node77_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 50 13 14 17 49), lower := (rows 7 50 13 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 14 50 12 14 16 32) }] }

theorem profile10_node77 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,6] 6 17 profile10_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,6] 6 17 profile10_node77_cert).mp (by decide +kernel))

def profile10_node78_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 7 50 13 25 22 38), lower := (rows 7 50 13 25 16 32), losses := [{ target := 0, region := (rows 0 15 4 8 21 37), good := (rows 54 50 62 58 16 32) }] }

theorem profile10_node78 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,17] 6 6 profile10_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,17] 6 6 profile10_node78_cert).mp (by decide +kernel))

def profile10_node79_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 50 13 26 21 37), lower := (rows 7 50 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 14 58 12 26 16 32) }] }

theorem profile10_node79 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,18] 6 5 profile10_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,18] 6 5 profile10_node79_cert).mp (by decide +kernel))

def profile10_node80_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 7 50 13 28 19 35), lower := (rows 7 50 13 28 16 32), losses := [{ target := 2, region := (rows 1 15 0 8 21 37), good := (rows 51 50 59 58 16 32) }] }

theorem profile10_node80 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,20] 6 3 profile10_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9,20] 6 3 profile10_node80_cert).mp (by decide +kernel))

def profile10_node74_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node74_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node74 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,9] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node74_route profile10_node74_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node75
  · exact profile10_node76
  · exact profile10_node77
  · exact profile10_node78
  · exact profile10_node79
  · exact profile10_node80

def profile10_node81_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 50 14 29 21 53), lower := (rows 7 50 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 48 12 8 16 32) }] }

theorem profile10_node81 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,10] 6 21 profile10_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,10] 6 21 profile10_node81_cert).mp (by decide +kernel))

def profile10_node82_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 50 21 15 31 47), lower := (rows 7 50 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 45 8 0 32) }] }

theorem profile10_node82 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,17] 6 15 profile10_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,17] 6 15 profile10_node82_cert).mp (by decide +kernel))

def profile10_node83_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 50 22 13 29 45), lower := (rows 7 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 22 8 16 32) }] }

theorem profile10_node83 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,18] 6 13 profile10_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,18] 6 13 profile10_node83_cert).mp (by decide +kernel))

def profile10_node84_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 50 28 15 23 39), lower := (rows 7 50 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 12 8 0 32) }] }

theorem profile10_node84 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,24] 6 7 profile10_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48,24] 6 7 profile10_node84_cert).mp (by decide +kernel))

def profile10_node72_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node72_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node72 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6,48] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node72_route profile10_node72_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node73
  · exact profile10_node74
  · exact profile10_node81
  · exact profile10_node82
  · exact profile10_node83
  · exact profile10_node84

def profile10_node1_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile10_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node1 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [6] 6 (by decide) (choices 2) [5,9,12,17,20,24,33,36,40,48] profile10_node1_route profile10_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node2
  · exact profile10_node3
  · exact profile10_node16
  · exact profile10_node17
  · exact profile10_node34
  · exact profile10_node35
  · exact profile10_node48
  · exact profile10_node61
  · exact profile10_node62
  · exact profile10_node72

def profile10_node87_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 7 7 60 52 52), lower := (rows 11 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 58 62 62 8 16 32) }] }

theorem profile10_node87 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,3] 6 52 profile10_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,3] 6 52 profile10_node87_cert).mp (by decide +kernel))

def profile10_node88_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 7 21 62 54 54), lower := (rows 11 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 20 8 16 32) }] }

theorem profile10_node88 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,17] 6 54 profile10_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,17] 6 54 profile10_node88_cert).mp (by decide +kernel))

def profile10_node89_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 11 7 22 61 53 53), lower := (rows 11 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node89 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,18] 6 53 profile10_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,18] 6 53 profile10_node89_cert).mp (by decide +kernel))

def profile10_node90_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 7 37 30 22 54), lower := (rows 11 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 36 8 16 32) }] }

theorem profile10_node90 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,33] 6 22 profile10_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,33] 6 22 profile10_node90_cert).mp (by decide +kernel))

def profile10_node91_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 11 7 38 29 21 53), lower := (rows 11 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node91 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,34] 6 21 profile10_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,34] 6 21 profile10_node91_cert).mp (by decide +kernel))

def profile10_node93_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 7 52 11 20 52), lower := (rows 11 7 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 62 54 52 62 52 52) }] }

theorem profile10_node93 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,3] 6 20 profile10_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,3] 6 20 profile10_node93_cert).mp (by decide +kernel))

def profile10_node94_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 7 52 13 18 50), lower := (rows 11 7 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 62 54 52 60 16 32) }] }

theorem profile10_node94 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,5] 6 18 profile10_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,5] 6 18 profile10_node94_cert).mp (by decide +kernel))

def profile10_node95_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 7 52 14 17 49), lower := (rows 11 7 52 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 10 14 52 14 16 32) }] }

theorem profile10_node95 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,6] 6 17 profile10_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,6] 6 17 profile10_node95_cert).mp (by decide +kernel))

def profile10_node96_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 7 52 25 22 38), lower := (rows 11 7 52 25 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 62 54 52 60 16 32) }] }

theorem profile10_node96 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,17] 6 6 profile10_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,17] 6 6 profile10_node96_cert).mp (by decide +kernel))

def profile10_node97_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 7 52 26 21 37), lower := (rows 11 7 52 26 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 61 53 52 60 16 32) }] }

theorem profile10_node97 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,18] 6 5 profile10_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,18] 6 5 profile10_node97_cert).mp (by decide +kernel))

def profile10_node98_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 7 52 28 19 35), lower := (rows 11 7 52 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 10 14 60 28 16 32) }] }

theorem profile10_node98 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,20] 6 3 profile10_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48,20] 6 3 profile10_node98_cert).mp (by decide +kernel))

def profile10_node92_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node92 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5,48] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node92_route profile10_node92_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node93
  · exact profile10_node94
  · exact profile10_node95
  · exact profile10_node96
  · exact profile10_node97
  · exact profile10_node98

def profile10_node86_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node86_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node86 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node86_route profile10_node86_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node87
  · exact profile10_node88
  · exact profile10_node89
  · exact profile10_node90
  · exact profile10_node91
  · exact profile10_node92

def profile10_node100_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 19 7 60 52 52), lower := (rows 11 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 10 18 62 8 16 32) }] }

theorem profile10_node100 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,3] 6 52 profile10_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,3] 6 52 profile10_node100_cert).mp (by decide +kernel))

def profile10_node101_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 19 21 46 54 38), lower := (rows 11 19 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 13 21 21 8 16 32) }] }

theorem profile10_node101 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,17] 6 38 profile10_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,17] 6 38 profile10_node101_cert).mp (by decide +kernel))

def profile10_node102_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 19 22 45 53 37), lower := (rows 11 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 14 22 22 8 16 32) }] }

theorem profile10_node102 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,18] 6 37 profile10_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,18] 6 37 profile10_node102_cert).mp (by decide +kernel))

def profile10_node104_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 19 37 14 20 52), lower := (rows 11 19 37 14 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 61 53 53 60 16 32) }] }

theorem profile10_node104 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,6] 6 20 profile10_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,6] 6 20 profile10_node104_cert).mp (by decide +kernel))

def profile10_node105_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 19 37 26 20 36), lower := (rows 11 19 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 20 36), good := (rows 10 26 52 26 16 32) }] }

theorem profile10_node105 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,18] 6 4 profile10_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,18] 6 4 profile10_node105_cert).mp (by decide +kernel))

def profile10_node106_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 11 19 37 28 22 38), lower := (rows 11 19 37 28 16 32), losses := [{ target := 2, region := (rows 9 10 0 8 16 32), good := (rows 11 19 33 27 16 32) }] }

theorem profile10_node106 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,20] 6 6 profile10_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33,20] 6 6 profile10_node106_cert).mp (by decide +kernel))

def profile10_node103_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node103_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node103 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,33] 6 (by decide) (choices 2) [6,18,20] profile10_node103_route profile10_node103_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node104
  · exact profile10_node105
  · exact profile10_node106

def profile10_node108_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 19 38 13 20 52), lower := (rows 11 19 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 62 54 54 60 16 32) }] }

theorem profile10_node108 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,5] 6 20 profile10_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,5] 6 20 profile10_node108_cert).mp (by decide +kernel))

def profile10_node109_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 19 38 25 20 36), lower := (rows 11 19 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 62 54 54 60 16 32) }] }

theorem profile10_node109 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,17] 6 4 profile10_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,17] 6 4 profile10_node109_cert).mp (by decide +kernel))

def profile10_node110_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 11 19 38 28 21 37), lower := (rows 11 19 38 28 16 32), losses := [{ target := 2, region := (rows 9 10 0 8 16 32), good := (rows 11 19 34 27 16 32) }] }

theorem profile10_node110 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,20] 6 5 profile10_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34,20] 6 5 profile10_node110_cert).mp (by decide +kernel))

def profile10_node107_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node107_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node107 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,34] 6 (by decide) (choices 2) [5,17,20] profile10_node107_route profile10_node107_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node108
  · exact profile10_node109
  · exact profile10_node110

def profile10_node112_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 19 52 11 20 36), lower := (rows 11 19 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 62 54 52 62 52 52) }] }

theorem profile10_node112 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,3] 6 4 profile10_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,3] 6 4 profile10_node112_cert).mp (by decide +kernel))

def profile10_node113_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 19 52 13 22 38), lower := (rows 11 19 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 62 54 52 60 16 32) }] }

theorem profile10_node113 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,5] 6 6 profile10_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,5] 6 6 profile10_node113_cert).mp (by decide +kernel))

def profile10_node114_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 19 52 14 21 37), lower := (rows 11 19 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 61 53 52 60 16 32) }] }

theorem profile10_node114 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,6] 6 5 profile10_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48,6] 6 5 profile10_node114_cert).mp (by decide +kernel))

def profile10_node111_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node111_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node111 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17,48] 6 (by decide) (choices 2) [3,5,6] profile10_node111_route profile10_node111_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node112
  · exact profile10_node113
  · exact profile10_node114

def profile10_node99_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node99_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node99 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node99_route profile10_node99_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node100
  · exact profile10_node101
  · exact profile10_node102
  · exact profile10_node103
  · exact profile10_node107
  · exact profile10_node111

def profile10_node116_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 11 22 7 61 53 53), lower := (rows 11 22 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 9 60 61 8 16 32) }] }

theorem profile10_node116 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,3] 6 53 profile10_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,3] 6 53 profile10_node116_cert).mp (by decide +kernel))

def profile10_node117_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 22 21 47 55 39), lower := (rows 11 22 21 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 10 22 22 8 16 32) }] }

theorem profile10_node117 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,17] 6 39 profile10_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,17] 6 39 profile10_node117_cert).mp (by decide +kernel))

def profile10_node118_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 11 22 22 45 53 37), lower := (rows 11 22 22 8 16 32), losses := [{ target := 0, region := (rows 0 22 22 8 16 32), good := (rows 14 22 22 8 22 32) }] }

theorem profile10_node118 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,18] 6 37 profile10_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,18] 6 37 profile10_node118_cert).mp (by decide +kernel))

def profile10_node120_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 22 37 11 20 52), lower := (rows 11 22 37 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 58 54 54 58 16 32) }] }

theorem profile10_node120 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,3] 6 20 profile10_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,3] 6 20 profile10_node120_cert).mp (by decide +kernel))

def profile10_node121_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 22 37 13 18 50), lower := (rows 11 22 37 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 58 54 54 62 16 32) }] }

theorem profile10_node121 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,5] 6 18 profile10_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,5] 6 18 profile10_node121_cert).mp (by decide +kernel))

def profile10_node122_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 22 37 14 17 49), lower := (rows 11 22 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 10 30 36 14 16 32) }] }

theorem profile10_node122 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,6] 6 17 profile10_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,6] 6 17 profile10_node122_cert).mp (by decide +kernel))

def profile10_node123_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 22 37 25 22 38), lower := (rows 11 22 37 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 58 54 54 24 16 32) }] }

theorem profile10_node123 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,17] 6 6 profile10_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,17] 6 6 profile10_node123_cert).mp (by decide +kernel))

def profile10_node124_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 22 37 26 21 37), lower := (rows 11 22 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 10 30 36 26 16 32) }] }

theorem profile10_node124 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,18] 6 5 profile10_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,18] 6 5 profile10_node124_cert).mp (by decide +kernel))

def profile10_node125_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 11 22 37 28 19 35), lower := (rows 11 22 37 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 10 30 36 30 16 32) }] }

theorem profile10_node125 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,20] 6 3 profile10_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33,20] 6 3 profile10_node125_cert).mp (by decide +kernel))

def profile10_node119_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node119_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node119 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,33] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node119_route profile10_node119_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node120
  · exact profile10_node121
  · exact profile10_node122
  · exact profile10_node123
  · exact profile10_node124
  · exact profile10_node125

def profile10_node127_cert : CutBound 6 := { lost := (rows 16 0 0 16 0 0), upper := (rows 11 22 38 13 17 49), lower := (rows 11 22 38 13 16 32), losses := [{ target := 4, region := (rows 7 2 4 14 0 32), good := (rows 11 15 47 13 0 32) }] }

theorem profile10_node127 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,5] 6 17 profile10_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,5] 6 17 profile10_node127_cert).mp (by decide +kernel))

def profile10_node128_cert : CutBound 6 := { lost := (rows 4 0 0 4 0 0), upper := (rows 11 22 38 25 21 37), lower := (rows 11 22 38 25 16 32), losses := [{ target := 2, region := (rows 7 2 0 10 16 32), good := (rows 11 27 43 25 16 32) }] }

theorem profile10_node128 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,17] 6 5 profile10_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,17] 6 5 profile10_node128_cert).mp (by decide +kernel))

def profile10_node129_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 11 22 38 28 17 33), lower := (rows 11 22 38 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 10 30 46 30 16 32) }] }

theorem profile10_node129 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,20] 6 1 profile10_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34,20] 6 1 profile10_node129_cert).mp (by decide +kernel))

def profile10_node126_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node126_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node126 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,34] 6 (by decide) (choices 2) [5,17,20] profile10_node126_route profile10_node126_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node127
  · exact profile10_node128
  · exact profile10_node129

def profile10_node130_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 22 52 15 23 39), lower := (rows 11 22 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 10 22 54 8 16 32) }] }

theorem profile10_node130 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,48] 6 7 profile10_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20,48] 6 7 profile10_node130_cert).mp (by decide +kernel))


#print axioms profile10_node130
end Delivery.SmallBudgetTenFinite6
