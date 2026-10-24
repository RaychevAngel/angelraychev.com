import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile7_node2_cert : CutBound 6 := { lost := (rows 0 0 0 4 4 0), upper := (rows 7 7 47 43 59 32), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) }] }

theorem profile7_node2 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,5] 6 43 profile7_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,5] 6 43 profile7_node2_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 7 11 7 45 53 32), lower := (rows 7 11 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) }] }

theorem profile7_node4 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,3] 6 37 profile7_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,3] 6 37 profile7_node4_cert).mp (by decide +kernel))

def profile7_node6_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 7 11 37 11 52 32), lower := (rows 7 11 37 11 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 21 63), good := (rows 54 58 52 58 48 32) },{ target := 1, region := (rows 1 0 15 8 31 63), good := (rows 53 61 53 61 48 32) }] }

theorem profile7_node6 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,3] 6 36 profile7_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,3] 6 36 profile7_node6_cert).mp (by decide +kernel))

def profile7_node7_cert : CutBound 6 := { lost := (rows 0 0 2 2 1 0), upper := (rows 7 11 37 13 50 32), lower := (rows 7 11 37 13 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 19 63), good := (rows 54 58 52 60 48 32) },{ target := 1, region := (rows 1 0 15 15 16 63), good := (rows 45 45 45 45 48 32) }] }

theorem profile7_node7 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,5] 6 34 profile7_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,5] 6 34 profile7_node7_cert).mp (by decide +kernel))

def profile7_node8_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 7 11 37 14 49 32), lower := (rows 7 11 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 63), good := (rows 46 42 44 46 48 32) },{ target := 1, region := (rows 1 0 7 8 23 63), good := (rows 53 61 53 60 48 32) }] }

theorem profile7_node8 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,6] 6 33 profile7_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,6] 6 33 profile7_node8_cert).mp (by decide +kernel))

def profile7_node9_cert : CutBound 6 := { lost := (rows 0 0 2 2 1 0), upper := (rows 7 11 37 41 22 32), lower := (rows 7 11 37 41 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 17 63), good := (rows 54 58 52 56 48 32) },{ target := 1, region := (rows 1 0 15 15 16 63), good := (rows 45 45 45 45 48 32) }] }

theorem profile7_node9 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,33] 6 6 profile7_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,33] 6 6 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 7 11 37 42 21 32), lower := (rows 7 11 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 16 63), good := (rows 46 42 44 42 48 32) },{ target := 1, region := (rows 1 0 7 8 23 63), good := (rows 53 61 53 60 48 32) }] }

theorem profile7_node10 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,34] 6 5 profile7_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,34] 6 5 profile7_node10_cert).mp (by decide +kernel))

def profile7_node11_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 7 11 37 44 19 32), lower := (rows 7 11 37 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 16 63), good := (rows 46 42 44 44 48 32) },{ target := 1, region := (rows 1 0 7 15 16 63), good := (rows 45 45 45 44 48 32) }] }

theorem profile7_node11 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,36] 6 3 profile7_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33,36] 6 3 profile7_node11_cert).mp (by decide +kernel))

def profile7_node5_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile7_node5_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node5 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,33] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile7_node5_route profile7_node5_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node6
  · exact profile7_node7
  · exact profile7_node8
  · exact profile7_node9
  · exact profile7_node10
  · exact profile7_node11

def profile7_node12_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 7 11 38 45 53 32), lower := (rows 7 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 46 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) }] }

theorem profile7_node12 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,34] 6 37 profile7_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9,34] 6 37 profile7_node12_cert).mp (by decide +kernel))

def profile7_node3_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile7_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node3 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,9] 6 (by decide) (choices 2) [3,33,34] profile7_node3_route profile7_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node4
  · exact profile7_node5
  · exact profile7_node12

def profile7_node13_cert : CutBound 6 := { lost := (rows 0 0 0 4 4 0), upper := (rows 7 14 39 43 51 32), lower := (rows 7 14 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 42 32 40 48 32) }] }

theorem profile7_node13 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,12] 6 35 profile7_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,12] 6 35 profile7_node13_cert).mp (by decide +kernel))

def profile7_node15_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 7 35 7 45 61 32), lower := (rows 7 35 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) }] }

theorem profile7_node15 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,3] 6 45 profile7_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,3] 6 45 profile7_node15_cert).mp (by decide +kernel))

def profile7_node17_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 7 35 13 11 52 32), lower := (rows 7 35 13 11 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 21 63), good := (rows 54 50 60 58 48 32) },{ target := 1, region := (rows 1 0 12 8 29 63), good := (rows 53 49 61 61 48 32) }] }

theorem profile7_node17 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,3] 6 36 profile7_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,3] 6 36 profile7_node17_cert).mp (by decide +kernel))

def profile7_node18_cert : CutBound 6 := { lost := (rows 0 0 2 2 1 0), upper := (rows 7 35 13 13 50 32), lower := (rows 7 35 13 13 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 19 63), good := (rows 54 50 60 60 48 32) },{ target := 1, region := (rows 1 0 15 15 16 63), good := (rows 45 45 45 45 48 32) }] }

theorem profile7_node18 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,5] 6 34 profile7_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,5] 6 34 profile7_node18_cert).mp (by decide +kernel))

def profile7_node19_cert : CutBound 6 := { lost := (rows 0 0 0 1 2 0), upper := (rows 7 35 13 14 49 32), lower := (rows 7 35 13 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 63), good := (rows 46 42 44 46 48 32) },{ target := 1, region := (rows 1 0 4 8 23 63), good := (rows 53 49 61 60 48 32) }] }

theorem profile7_node19 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,6] 6 33 profile7_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,6] 6 33 profile7_node19_cert).mp (by decide +kernel))

def profile7_node20_cert : CutBound 6 := { lost := (rows 0 0 2 2 1 0), upper := (rows 7 35 13 41 22 32), lower := (rows 7 35 13 41 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 17 63), good := (rows 54 50 60 56 48 32) },{ target := 1, region := (rows 1 0 15 15 16 63), good := (rows 45 45 45 45 48 32) }] }

theorem profile7_node20 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,33] 6 6 profile7_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,33] 6 6 profile7_node20_cert).mp (by decide +kernel))

def profile7_node21_cert : CutBound 6 := { lost := (rows 0 0 0 1 2 0), upper := (rows 7 35 13 42 21 32), lower := (rows 7 35 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 16 63), good := (rows 46 42 44 42 48 32) },{ target := 1, region := (rows 1 0 4 8 21 63), good := (rows 53 49 61 40 48 32) }] }

theorem profile7_node21 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,34] 6 5 profile7_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,34] 6 5 profile7_node21_cert).mp (by decide +kernel))

def profile7_node22_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 7 35 13 44 19 32), lower := (rows 7 35 13 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 16 63), good := (rows 46 42 44 44 48 32) },{ target := 1, region := (rows 1 0 7 15 16 63), good := (rows 45 45 45 44 48 32) }] }

theorem profile7_node22 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,36] 6 3 profile7_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9,36] 6 3 profile7_node22_cert).mp (by decide +kernel))

def profile7_node16_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile7_node16_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node16 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,9] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile7_node16_route profile7_node16_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node17
  · exact profile7_node18
  · exact profile7_node19
  · exact profile7_node20
  · exact profile7_node21
  · exact profile7_node22

def profile7_node23_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 7 35 14 45 53 32), lower := (rows 7 35 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 44 40 48 32) }] }

theorem profile7_node23 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,10] 6 37 profile7_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,10] 6 37 profile7_node23_cert).mp (by decide +kernel))

def profile7_node24_cert : CutBound 6 := { lost := (rows 0 4 2 0 0 0), upper := (rows 7 35 37 15 31 32), lower := (rows 7 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 35 35 35 40 48 32) }] }

theorem profile7_node24 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,33] 6 15 profile7_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,33] 6 15 profile7_node24_cert).mp (by decide +kernel))

def profile7_node25_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 7 35 38 13 29 32), lower := (rows 7 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) }] }

theorem profile7_node25 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,34] 6 13 profile7_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,34] 6 13 profile7_node25_cert).mp (by decide +kernel))

def profile7_node26_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 35 44 15 23 32), lower := (rows 7 35 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 38 34 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 37 33 44 44 48 32) }] }

theorem profile7_node26 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,40] 6 7 profile7_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33,40] 6 7 profile7_node26_cert).mp (by decide +kernel))

def profile7_node14_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile7_node14_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node14 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,33] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile7_node14_route profile7_node14_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node15
  · exact profile7_node16
  · exact profile7_node23
  · exact profile7_node24
  · exact profile7_node25
  · exact profile7_node26

def profile7_node27_cert : CutBound 6 := { lost := (rows 0 1 0 4 4 0), upper := (rows 7 38 47 43 59 32), lower := (rows 7 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile7_node27 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,36] 6 43 profile7_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,36] 6 43 profile7_node27_cert).mp (by decide +kernel))

def profile7_node28_cert : CutBound 6 := { lost := (rows 0 5 0 0 0 0), upper := (rows 7 42 39 47 55 32), lower := (rows 7 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 36 42 48 32) },{ target := 2, region := (rows 1 10 0 8 16 63), good := (rows 35 42 32 42 48 32) }] }

theorem profile7_node28 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,40] 6 39 profile7_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6,40] 6 39 profile7_node28_cert).mp (by decide +kernel))

def profile7_node1_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile7_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [6] 6 (by decide) (choices 2) [5,9,12,33,36,40] profile7_node1_route profile7_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node13
  · exact profile7_node14
  · exact profile7_node27
  · exact profile7_node28

def profile7_node31_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 11 7 7 45 53 32), lower := (rows 11 7 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) }] }

theorem profile7_node31 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,3] 6 37 profile7_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,3] 6 37 profile7_node31_cert).mp (by decide +kernel))

def profile7_node32_cert : CutBound 6 := { lost := (rows 0 32 2 0 0 0), upper := (rows 11 7 37 47 55 32), lower := (rows 11 7 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 45 37 37 40 48 32) },{ target := 5, region := (rows 1 6 4 8 16 0), good := (rows 11 7 7 8 16 0) }] }

theorem profile7_node32 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,33] 6 39 profile7_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,33] 6 39 profile7_node32_cert).mp (by decide +kernel))

def profile7_node33_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 11 7 38 45 53 32), lower := (rows 11 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 46 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile7_node33 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,34] 6 37 profile7_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5,34] 6 37 profile7_node33_cert).mp (by decide +kernel))

def profile7_node30_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile7_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node30 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,5] 6 (by decide) (choices 2) [3,33,34] profile7_node30_route profile7_node30_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node31
  · exact profile7_node32
  · exact profile7_node33

def profile7_node34_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 11 35 39 47 55 32), lower := (rows 11 35 4 8 16 32), losses := [{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 32 43 48 32) }] }

theorem profile7_node34 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,33] 6 39 profile7_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,33] 6 39 profile7_node34_cert).mp (by decide +kernel))

def profile7_node36_cert : CutBound 6 := { lost := (rows 0 1 0 2 2 0), upper := (rows 11 38 7 45 53 32), lower := (rows 11 38 7 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 42 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 41 60 61 40 48 32) }] }

theorem profile7_node36 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,3] 6 37 profile7_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,3] 6 37 profile7_node36_cert).mp (by decide +kernel))

def profile7_node37_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 11 38 37 15 23 32), lower := (rows 11 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 42 38 38 40 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 45 36 37 40 48 32) }] }

theorem profile7_node37 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,33] 6 7 profile7_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,33] 6 7 profile7_node37_cert).mp (by decide +kernel))

def profile7_node38_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 11 38 38 13 21 32), lower := (rows 11 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 46 38 38 46 54 38) }] }

theorem profile7_node38 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,34] 6 5 profile7_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36,34] 6 5 profile7_node38_cert).mp (by decide +kernel))

def profile7_node35_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile7_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node35 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10,36] 6 (by decide) (choices 2) [3,33,34] profile7_node35_route profile7_node35_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node36
  · exact profile7_node37
  · exact profile7_node38

def profile7_node29_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile7_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node29 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [10] 6 (by decide) (choices 2) [5,33,36] profile7_node29_route profile7_node29_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node30
  · exact profile7_node34
  · exact profile7_node35

def profile7_node41_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 35 7 7 45 61 32), lower := (rows 35 7 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) }] }

theorem profile7_node41 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,3] 6 45 profile7_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,3] 6 45 profile7_node41_cert).mp (by decide +kernel))

def profile7_node42_cert : CutBound 6 := { lost := (rows 4 32 0 0 0 0), upper := (rows 35 7 13 47 55 32), lower := (rows 35 7 13 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 41 40 48 32) },{ target := 5, region := (rows 1 6 4 8 16 0), good := (rows 3 7 15 8 16 0) }] }

theorem profile7_node42 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,9] 6 39 profile7_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,9] 6 39 profile7_node42_cert).mp (by decide +kernel))

def profile7_node43_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 35 7 14 45 53 32), lower := (rows 35 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile7_node43 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,10] 6 37 profile7_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,10] 6 37 profile7_node43_cert).mp (by decide +kernel))

def profile7_node44_cert : CutBound 6 := { lost := (rows 4 0 2 0 0 0), upper := (rows 35 7 37 15 31 32), lower := (rows 35 7 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 33 40 48 32) }] }

theorem profile7_node44 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,33] 6 15 profile7_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,33] 6 15 profile7_node44_cert).mp (by decide +kernel))

def profile7_node45_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 35 7 38 13 29 32), lower := (rows 35 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile7_node45 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,34] 6 13 profile7_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,34] 6 13 profile7_node45_cert).mp (by decide +kernel))

def profile7_node46_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 35 7 44 15 23 32), lower := (rows 35 7 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 34 38 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 33 37 44 44 48 32) }] }

theorem profile7_node46 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,40] 6 7 profile7_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5,40] 6 7 profile7_node46_cert).mp (by decide +kernel))

def profile7_node40_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile7_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node40 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,5] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile7_node40_route profile7_node40_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node41
  · exact profile7_node42
  · exact profile7_node43
  · exact profile7_node44
  · exact profile7_node45
  · exact profile7_node46

def profile7_node47_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 35 11 39 47 55 32), lower := (rows 35 11 4 8 16 32), losses := [{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 32 43 48 32) }] }

theorem profile7_node47 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,9] 6 39 profile7_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,9] 6 39 profile7_node47_cert).mp (by decide +kernel))

def profile7_node49_cert : CutBound 6 := { lost := (rows 0 0 0 2 2 0), upper := (rows 35 14 7 45 53 32), lower := (rows 35 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 33 60 61 40 48 32) }] }

theorem profile7_node49 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,3] 6 37 profile7_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,3] 6 37 profile7_node49_cert).mp (by decide +kernel))

def profile7_node50_cert : CutBound 6 := { lost := (rows 4 0 2 0 0 0), upper := (rows 35 14 37 15 23 32), lower := (rows 35 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 44 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 33 40 48 32) }] }

theorem profile7_node50 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,33] 6 7 profile7_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,33] 6 7 profile7_node50_cert).mp (by decide +kernel))

def profile7_node51_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 35 14 38 13 21 32), lower := (rows 35 14 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) }] }

theorem profile7_node51 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,34] 6 5 profile7_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12,34] 6 5 profile7_node51_cert).mp (by decide +kernel))

def profile7_node48_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile7_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node48 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,12] 6 (by decide) (choices 2) [3,33,34] profile7_node48_route profile7_node48_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node49
  · exact profile7_node50
  · exact profile7_node51

def profile7_node52_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 35 35 15 15 31 32), lower := (rows 35 35 4 8 16 32), losses := [{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) }] }

theorem profile7_node52 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,33] 6 15 profile7_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,33] 6 15 profile7_node52_cert).mp (by decide +kernel))

def profile7_node53_cert : CutBound 6 := { lost := (rows 4 1 0 0 0 0), upper := (rows 35 38 15 15 31 32), lower := (rows 35 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 34 38 38 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 32 40 48 32) }] }

theorem profile7_node53 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,36] 6 15 profile7_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,36] 6 15 profile7_node53_cert).mp (by decide +kernel))

def profile7_node54_cert : CutBound 6 := { lost := (rows 4 5 0 0 0 0), upper := (rows 35 42 7 15 23 32), lower := (rows 35 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 34 42 36 42 48 32) },{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 32 43 48 32) }] }

theorem profile7_node54 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,40] 6 7 profile7_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34,40] 6 7 profile7_node54_cert).mp (by decide +kernel))

def profile7_node39_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile7_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile7_node39 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [34] 6 (by decide) (choices 2) [5,9,12,33,36,40] profile7_node39_route profile7_node39_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node40
  · exact profile7_node47
  · exact profile7_node48
  · exact profile7_node52
  · exact profile7_node53
  · exact profile7_node54

def profile7_node55_cert : CutBound 6 := { lost := (rows 6 0 0 0 0 0), upper := (rows 41 39 39 47 55 32), lower := (rows 41 2 4 8 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 32 36 41 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 34 32 41 48 32) }] }

theorem profile7_node55 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [40] 6 39 profile7_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [40] 6 39 profile7_node55_cert).mp (by decide +kernel))

def profile7_node0_column : Nat → Fin 6 := fun mask => match mask with | 18 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile7_node0_route : Route 6 := (fun mask => match mask with | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile7_node0 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [] 6 (by decide) (choices 2) [6,10,34,40] profile7_node0_route profile7_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node1
  · exact profile7_node29
  · exact profile7_node39
  · exact profile7_node55

theorem profile7 : Upper (D (n:=6) [35,34,34,33,32,2]) (R (n:=6) [35,34,34,33,32,2]) [] 6 := profile7_node0


#print axioms profile7
end Delivery.SmallBudgetTenFinite6
