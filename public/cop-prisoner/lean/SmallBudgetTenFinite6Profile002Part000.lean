import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile2_node2_cert : CutBound 6 := { lost := (rows 0 16 0 4 0 0), upper := (rows 23 7 55 59 51 32), lower := (rows 23 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) },{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 39 39 36 40 32 32) }] }

theorem profile2_node2 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,5] 6 51 profile2_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,5] 6 51 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 6 := { lost := (rows 0 4 16 16 0 0), upper := (rows 23 19 39 47 55 32), lower := (rows 23 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 51 51 32 40 48 32) },{ target := 4, region := (rows 1 2 7 11 0 63), good := (rows 47 47 36 40 32 32) }] }

theorem profile2_node3 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,17] 6 39 profile2_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,17] 6 39 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 6 := { lost := (rows 0 1 0 4 0 0), upper := (rows 23 22 39 43 51 32), lower := (rows 23 22 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 63), good := (rows 54 54 36 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 50 32 40 48 32) }] }

theorem profile2_node4 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,20] 6 35 profile2_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,20] 6 35 profile2_node4_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 6 := { lost := (rows 0 20 0 0 0 0), upper := (rows 23 35 55 63 55 32), lower := (rows 23 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 51 35 32 40 48 32) },{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 39 35 36 40 32 32) }] }

theorem profile2_node5 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,33] 6 55 profile2_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,33] 6 55 profile2_node5_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 6 := { lost := (rows 0 1 0 4 0 0), upper := (rows 23 38 55 59 51 32), lower := (rows 23 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 54 38 38 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile2_node6 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,36] 6 51 profile2_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,36] 6 51 profile2_node6_cert).mp (by decide +kernel))

def profile2_node7_cert : CutBound 6 := { lost := (rows 0 5 0 0 0 0), upper := (rows 23 50 39 47 55 32), lower := (rows 23 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 54 50 36 40 50 32) },{ target := 2, region := (rows 1 19 0 8 16 63), good := (rows 51 50 32 40 50 32) }] }

theorem profile2_node7 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,48] 6 39 profile2_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22,48] 6 39 profile2_node7_cert).mp (by decide +kernel))

def profile2_node1_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile2_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [22] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile2_node1_route profile2_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node5
  · exact profile2_node6
  · exact profile2_node7

def profile2_node9_cert : CutBound 6 := { lost := (rows 16 16 0 4 0 0), upper := (rows 39 7 55 59 51 32), lower := (rows 39 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 63), good := (rows 59 59 32 40 48 32) },{ target := 4, region := (rows 7 7 4 8 0 63), good := (rows 39 39 39 40 32 32) }] }

theorem profile2_node9 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,5] 6 51 profile2_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,5] 6 51 profile2_node9_cert).mp (by decide +kernel))

def profile2_node11_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 39 19 7 60 52 32), lower := (rows 39 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 63), good := (rows 62 58 62 40 48 32) },{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 57 61 40 48 32) }] }

theorem profile2_node11 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,3] 6 52 profile2_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,3] 6 52 profile2_node11_cert).mp (by decide +kernel))

def profile2_node12_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 39 19 21 46 54 32), lower := (rows 39 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 6 8 16 63), good := (rows 37 53 53 40 48 32) }] }

theorem profile2_node12 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,17] 6 38 profile2_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,17] 6 38 profile2_node12_cert).mp (by decide +kernel))

def profile2_node13_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 39 19 22 45 53 32), lower := (rows 39 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 38 54 54 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 52 40 48 32) }] }

theorem profile2_node13 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,18] 6 37 profile2_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,18] 6 37 profile2_node13_cert).mp (by decide +kernel))

def profile2_node14_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 39 19 37 30 22 32), lower := (rows 39 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 63), good := (rows 62 58 60 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 53 37 40 48 32) }] }

theorem profile2_node14 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,33] 6 22 profile2_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,33] 6 22 profile2_node14_cert).mp (by decide +kernel))

def profile2_node15_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 39 19 38 29 21 32), lower := (rows 39 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 54 38 40 48 32) },{ target := 1, region := (rows 1 0 4 9 17 63), good := (rows 61 57 36 40 48 32) }] }

theorem profile2_node15 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,34] 6 21 profile2_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,34] 6 21 profile2_node15_cert).mp (by decide +kernel))

def profile2_node16_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 39 19 52 15 23 32), lower := (rows 39 19 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 22 8 16 63), good := (rows 38 54 52 40 52 32) },{ target := 1, region := (rows 1 0 22 8 16 63), good := (rows 37 53 52 40 52 32) }] }

theorem profile2_node16 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,48] 6 7 profile2_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17,48] 6 7 profile2_node16_cert).mp (by decide +kernel))

def profile2_node10_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile2_node10_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node10 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile2_node10_route profile2_node10_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node11
  · exact profile2_node12
  · exact profile2_node13
  · exact profile2_node14
  · exact profile2_node15
  · exact profile2_node16

def profile2_node17_cert : CutBound 6 := { lost := (rows 16 0 0 4 0 0), upper := (rows 39 22 55 59 51 32), lower := (rows 39 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 50 32 40 48 32) },{ target := 4, region := (rows 3 2 4 8 0 63), good := (rows 39 39 36 40 32 32) }] }

theorem profile2_node17 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,20] 6 51 profile2_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,20] 6 51 profile2_node17_cert).mp (by decide +kernel))

def profile2_node18_cert : CutBound 6 := { lost := (rows 16 20 0 0 0 0), upper := (rows 39 35 23 31 23 32), lower := (rows 39 35 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 35 35 32 40 48 32) },{ target := 4, region := (rows 5 7 4 8 0 63), good := (rows 39 35 39 40 32 32) }] }

theorem profile2_node18 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,33] 6 23 profile2_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,33] 6 23 profile2_node18_cert).mp (by decide +kernel))

def profile2_node19_cert : CutBound 6 := { lost := (rows 0 1 0 4 0 0), upper := (rows 39 38 23 27 19 32), lower := (rows 39 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 7 4 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 2, region := (rows 1 2 0 9 17 63), good := (rows 59 34 32 40 48 32) }] }

theorem profile2_node19 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,36] 6 19 profile2_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,36] 6 19 profile2_node19_cert).mp (by decide +kernel))

def profile2_node20_cert : CutBound 6 := { lost := (rows 0 5 0 0 0 0), upper := (rows 39 50 23 31 23 32), lower := (rows 39 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 38 50 36 40 50 32) },{ target := 2, region := (rows 1 18 0 8 16 63), good := (rows 35 50 32 40 50 32) }] }

theorem profile2_node20 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,48] 6 23 profile2_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38,48] 6 23 profile2_node20_cert).mp (by decide +kernel))

def profile2_node8_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile2_node8_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node8 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [38] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile2_node8_route profile2_node8_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node9
  · exact profile2_node10
  · exact profile2_node17
  · exact profile2_node18
  · exact profile2_node19
  · exact profile2_node20

def profile2_node23_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 51 7 7 60 52 32), lower := (rows 51 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 58 62 62 40 48 32) },{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) }] }

theorem profile2_node23 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,3] 6 52 profile2_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,3] 6 52 profile2_node23_cert).mp (by decide +kernel))

def profile2_node24_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 51 7 21 46 54 32), lower := (rows 51 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 52 40 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 53 37 53 40 48 32) }] }

theorem profile2_node24 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,17] 6 38 profile2_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,17] 6 38 profile2_node24_cert).mp (by decide +kernel))

def profile2_node25_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 51 7 22 45 53 32), lower := (rows 51 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 63), good := (rows 54 38 54 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile2_node25 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,18] 6 37 profile2_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,18] 6 37 profile2_node25_cert).mp (by decide +kernel))

def profile2_node26_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 51 7 37 30 22 32), lower := (rows 51 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 36 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 53 37 37 40 48 32) }] }

theorem profile2_node26 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,33] 6 22 profile2_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,33] 6 22 profile2_node26_cert).mp (by decide +kernel))

def profile2_node27_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 51 7 38 29 21 32), lower := (rows 51 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 54 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile2_node27 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,34] 6 21 profile2_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,34] 6 21 profile2_node27_cert).mp (by decide +kernel))

def profile2_node28_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 51 7 52 15 23 32), lower := (rows 51 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 21 8 16 63), good := (rows 54 38 52 40 52 32) },{ target := 1, region := (rows 1 0 21 8 16 63), good := (rows 53 37 52 40 52 32) }] }

theorem profile2_node28 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,48] 6 7 profile2_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5,48] 6 7 profile2_node28_cert).mp (by decide +kernel))

def profile2_node22_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile2_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node22 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile2_node22_route profile2_node22_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node23
  · exact profile2_node24
  · exact profile2_node25
  · exact profile2_node26
  · exact profile2_node27
  · exact profile2_node28

def profile2_node29_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 51 19 39 47 55 32), lower := (rows 51 19 4 8 16 32), losses := [{ target := 2, region := (rows 19 19 0 8 16 63), good := (rows 51 51 32 40 51 32) }] }

theorem profile2_node29 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,17] 6 39 profile2_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,17] 6 39 profile2_node29_cert).mp (by decide +kernel))

def profile2_node30_cert : CutBound 6 := { lost := (rows 4 0 16 16 0 0), upper := (rows 51 22 39 47 55 32), lower := (rows 51 22 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 51 51 32 40 48 32) },{ target := 4, region := (rows 1 2 5 9 0 63), good := (rows 47 38 36 40 32 32) }] }

theorem profile2_node30 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,20] 6 39 profile2_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,20] 6 39 profile2_node30_cert).mp (by decide +kernel))

def profile2_node31_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 51 35 23 31 23 32), lower := (rows 51 35 4 8 16 32), losses := [{ target := 2, region := (rows 17 19 0 8 16 63), good := (rows 51 35 32 40 51 32) }] }

theorem profile2_node31 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,33] 6 23 profile2_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,33] 6 23 profile2_node31_cert).mp (by decide +kernel))

def profile2_node32_cert : CutBound 6 := { lost := (rows 0 17 0 0 0 0), upper := (rows 51 38 23 31 23 32), lower := (rows 51 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 50 38 38 40 48 32) },{ target := 4, region := (rows 1 6 4 8 0 63), good := (rows 35 38 38 40 32 32) }] }

theorem profile2_node32 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,36] 6 23 profile2_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,36] 6 23 profile2_node32_cert).mp (by decide +kernel))

def profile2_node33_cert : CutBound 6 := { lost := (rows 4 5 0 0 0 0), upper := (rows 51 50 7 15 23 32), lower := (rows 51 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 50 50 36 40 50 32) },{ target := 2, region := (rows 19 19 0 8 16 63), good := (rows 51 51 32 40 51 32) }] }

theorem profile2_node33 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,48] 6 7 profile2_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50,48] 6 7 profile2_node33_cert).mp (by decide +kernel))

def profile2_node21_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile2_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile2_node21 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [50] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile2_node21_route profile2_node21_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node22
  · exact profile2_node29
  · exact profile2_node30
  · exact profile2_node31
  · exact profile2_node32
  · exact profile2_node33

def profile2_node0_column : Nat → Fin 6 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 28 => 3 | 44 => 3 | 56 => 3 | _ => 0

def profile2_node0_route : Route 6 := (fun mask => match mask with | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [] 6 (by decide) (choices 3) [22,38,50] profile2_node0_route profile2_node0_column
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node1
  · exact profile2_node8
  · exact profile2_node21

theorem profile2 : Upper (D (n:=6) [50,34,34,32,18,2]) (R (n:=6) [50,34,34,32,18,2]) [] 6 := profile2_node0


#print axioms profile2
end Delivery.SmallBudgetTenFinite6
