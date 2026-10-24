import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile12_node2_cert : CutBound 6 := { lost := (rows 16 16 0 4 0 0), upper := (rows 7 7 55 59 51 51), lower := (rows 7 7 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 11 19 35), good := (rows 59 59 0 8 16 32) },{ target := 4, region := (rows 7 7 4 8 0 32), good := (rows 7 7 7 8 0 32) }] }

theorem profile12_node2 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,5] 6 51 profile12_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,5] 6 51 profile12_node2_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 6 := { lost := (rows 16 0 16 3 0 0), upper := (rows 7 19 7 60 52 52), lower := (rows 7 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 21 37), good := (rows 62 58 62 8 16 32) },{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 57 61 8 16 32) },{ target := 4, region := (rows 7 2 7 8 0 32), good := (rows 7 7 7 8 0 32) }] }

theorem profile12_node4 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,3] 6 52 profile12_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,3] 6 52 profile12_node4_cert).mp (by decide +kernel))

def profile12_node5_cert : CutBound 6 := { lost := (rows 0 4 2 1 0 0), upper := (rows 7 19 21 46 54 38), lower := (rows 7 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 17 33), good := (rows 62 58 60 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 5 21 21 8 16 32) },{ target := 2, region := (rows 1 6 0 8 16 32), good := (rows 3 19 19 8 16 32) }] }

theorem profile12_node5 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,17] 6 38 profile12_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,17] 6 38 profile12_node5_cert).mp (by decide +kernel))

def profile12_node6_cert : CutBound 6 := { lost := (rows 16 0 1 18 0 0), upper := (rows 7 19 22 45 53 37), lower := (rows 7 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 22 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 20 8 16 32) },{ target := 4, region := (rows 5 2 4 13 0 37), good := (rows 47 43 47 8 0 32) }] }

theorem profile12_node6 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,18] 6 37 profile12_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,18] 6 37 profile12_node6_cert).mp (by decide +kernel))

def profile12_node8_cert : CutBound 6 := { lost := (rows 0 4 2 1 0 0), upper := (rows 7 19 37 14 48 48), lower := (rows 7 19 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 63 63), good := (rows 62 58 60 62 48 48) },{ target := 1, region := (rows 1 0 7 8 63 63), good := (rows 53 53 53 60 48 48) },{ target := 2, region := (rows 1 7 0 8 63 63), good := (rows 51 51 51 58 48 48) }] }

theorem profile12_node8 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,6] 6 48 profile12_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,6] 6 48 profile12_node8_cert).mp (by decide +kernel))

def profile12_node9_cert : CutBound 6 := { lost := (rows 0 0 2 5 0 0), upper := (rows 7 19 37 26 52 36), lower := (rows 7 19 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 21 37), good := (rows 62 58 60 26 16 32) },{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 53 53 53 60 16 32) },{ target := 2, region := (rows 1 2 0 10 16 32), good := (rows 11 27 33 26 16 32) }] }

theorem profile12_node9 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,18] 6 36 profile12_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,18] 6 36 profile12_node9_cert).mp (by decide +kernel))

def profile12_node10_cert : CutBound 6 := { lost := (rows 16 4 16 1 0 0), upper := (rows 7 19 37 28 50 34), lower := (rows 7 19 37 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 19 35), good := (rows 62 58 60 28 16 32) },{ target := 2, region := (rows 1 7 0 8 31 47), good := (rows 51 51 51 58 16 32) },{ target := 4, region := (rows 3 2 7 8 0 35), good := (rows 39 39 37 12 0 32) }] }

theorem profile12_node10 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,20] 6 34 profile12_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,20] 6 34 profile12_node10_cert).mp (by decide +kernel))

def profile12_node11_cert : CutBound 6 := { lost := (rows 16 0 18 1 0 0), upper := (rows 7 19 37 42 20 52), lower := (rows 7 19 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 21 37), good := (rows 62 58 60 42 16 32) },{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 53 53 53 60 16 32) },{ target := 4, region := (rows 9 2 12 8 0 32), good := (rows 7 3 37 47 0 32) }] }

theorem profile12_node11 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,34] 6 20 profile12_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,34] 6 20 profile12_node11_cert).mp (by decide +kernel))

def profile12_node12_cert : CutBound 6 := { lost := (rows 0 4 0 3 0 0), upper := (rows 7 19 37 44 18 50), lower := (rows 7 19 37 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 13 19 35), good := (rows 62 58 60 44 16 32) },{ target := 1, region := (rows 1 0 4 12 16 32), good := (rows 13 17 45 44 16 32) },{ target := 2, region := (rows 1 7 0 8 31 47), good := (rows 51 51 51 58 16 32) }] }

theorem profile12_node12 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,36] 6 18 profile12_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,36] 6 18 profile12_node12_cert).mp (by decide +kernel))

def profile12_node13_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 7 19 37 56 22 38), lower := (rows 7 19 37 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 15 17 33), good := (rows 62 58 60 56 16 32) },{ target := 4, region := (rows 3 2 7 8 0 35), good := (rows 39 39 37 40 0 32) }] }

theorem profile12_node13 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,48] 6 6 profile12_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33,48] 6 6 profile12_node13_cert).mp (by decide +kernel))

def profile12_node7_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | _ => 0

def profile12_node7_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node7 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,33] 6 (by decide) (choices 2) [6,18,20,34,36,48] profile12_node7_route profile12_node7_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node8
  · exact profile12_node9
  · exact profile12_node10
  · exact profile12_node11
  · exact profile12_node12
  · exact profile12_node13

def profile12_node14_cert : CutBound 6 := { lost := (rows 48 0 0 2 0 0), upper := (rows 7 19 38 61 53 53), lower := (rows 7 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 57 36 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 3 39 8 0 32) },{ target := 5, region := (rows 5 2 4 8 16 0), good := (rows 7 19 7 8 16 0) }] }

theorem profile12_node14 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,34] 6 53 profile12_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,34] 6 53 profile12_node14_cert).mp (by decide +kernel))

def profile12_node15_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 7 19 52 47 55 39), lower := (rows 7 19 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 43 36 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 7 19 23 8 16 0) }] }

theorem profile12_node15 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,48] 6 39 profile12_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17,48] 6 39 profile12_node15_cert).mp (by decide +kernel))

def profile12_node3_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node3_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node3 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile12_node3_route profile12_node3_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node4
  · exact profile12_node5
  · exact profile12_node6
  · exact profile12_node7
  · exact profile12_node14
  · exact profile12_node15

def profile12_node16_cert : CutBound 6 := { lost := (rows 48 0 0 4 0 0), upper := (rows 7 22 55 59 51 51), lower := (rows 7 22 4 8 16 32), losses := [{ target := 2, region := (rows 1 2 0 9 17 33), good := (rows 59 18 0 8 16 32) },{ target := 4, region := (rows 3 2 4 8 0 32), good := (rows 7 7 4 8 0 32) },{ target := 5, region := (rows 3 2 4 8 16 0), good := (rows 7 23 4 8 16 0) }] }

theorem profile12_node16 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,20] 6 51 profile12_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,20] 6 51 profile12_node16_cert).mp (by decide +kernel))

def profile12_node18_cert : CutBound 6 := { lost := (rows 16 0 16 2 0 0), upper := (rows 7 50 7 61 53 53), lower := (rows 7 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 48 61 8 16 32) },{ target := 4, region := (rows 7 2 7 8 0 32), good := (rows 7 39 7 8 0 32) }] }

theorem profile12_node18 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,3] 6 53 profile12_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,3] 6 53 profile12_node18_cert).mp (by decide +kernel))

def profile12_node19_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 7 50 21 47 55 39), lower := (rows 7 50 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 45 8 0 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 7 23 21 8 16 0) }] }

theorem profile12_node19 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,17] 6 39 profile12_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,17] 6 39 profile12_node19_cert).mp (by decide +kernel))

def profile12_node20_cert : CutBound 6 := { lost := (rows 16 0 1 18 0 0), upper := (rows 7 50 22 45 53 37), lower := (rows 7 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 48 20 8 16 32) },{ target := 4, region := (rows 5 2 4 13 0 37), good := (rows 47 34 47 8 0 32) }] }

theorem profile12_node20 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,18] 6 37 profile12_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,18] 6 37 profile12_node20_cert).mp (by decide +kernel))

def profile12_node21_cert : CutBound 6 := { lost := (rows 0 1 3 0 0 0), upper := (rows 7 50 52 15 23 39), lower := (rows 7 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 6 54 54 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 5 52 52 8 16 32) }] }

theorem profile12_node21 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,48] 6 7 profile12_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48,48] 6 7 profile12_node21_cert).mp (by decide +kernel))

def profile12_node17_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node17_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile12_node17 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6,48] 6 (by decide) (choices 2) [3,17,18,48] profile12_node17_route profile12_node17_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node18
  · exact profile12_node19
  · exact profile12_node20
  · exact profile12_node21

def profile12_node1_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node1_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile12_node1 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [6] 6 (by decide) (choices 2) [5,17,20,48] profile12_node1_route profile12_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node16
  · exact profile12_node17

def profile12_node24_cert : CutBound 6 := { lost := (rows 0 16 16 3 0 0), upper := (rows 19 7 7 60 52 52), lower := (rows 19 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 58 62 62 8 16 32) },{ target := 1, region := (rows 1 0 4 14 22 38), good := (rows 57 61 61 8 16 32) },{ target := 4, region := (rows 1 7 7 8 0 32), good := (rows 7 7 7 8 0 32) }] }

theorem profile12_node24 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,3] 6 52 profile12_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,3] 6 52 profile12_node24_cert).mp (by decide +kernel))

def profile12_node25_cert : CutBound 6 := { lost := (rows 0 16 2 17 0 0), upper := (rows 19 7 21 46 54 38), lower := (rows 19 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 20 8 16 32) },{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 5 21 8 16 32) },{ target := 4, region := (rows 1 6 4 14 0 38), good := (rows 43 47 47 8 0 32) }] }

theorem profile12_node25 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,17] 6 38 profile12_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,17] 6 38 profile12_node25_cert).mp (by decide +kernel))

def profile12_node26_cert : CutBound 6 := { lost := (rows 4 0 1 2 0 0), upper := (rows 19 7 22 45 53 37), lower := (rows 19 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 6 22 8 16 32) },{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) },{ target := 2, region := (rows 5 2 0 8 16 32), good := (rows 19 3 19 8 16 32) }] }

theorem profile12_node26 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,18] 6 37 profile12_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,18] 6 37 profile12_node26_cert).mp (by decide +kernel))

def profile12_node27_cert : CutBound 6 := { lost := (rows 0 48 0 1 0 0), upper := (rows 19 7 37 62 54 54), lower := (rows 19 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 36 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 7 39 8 0 32) },{ target := 5, region := (rows 1 6 4 8 16 0), good := (rows 19 7 7 8 16 0) }] }

theorem profile12_node27 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,33] 6 54 profile12_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,33] 6 54 profile12_node27_cert).mp (by decide +kernel))

def profile12_node29_cert : CutBound 6 := { lost := (rows 4 0 1 2 0 0), upper := (rows 19 7 38 13 48 48), lower := (rows 19 7 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 63 63), good := (rows 54 54 54 60 48 48) },{ target := 1, region := (rows 1 0 4 10 63 63), good := (rows 57 61 60 61 48 48) },{ target := 2, region := (rows 7 2 0 8 63 63), good := (rows 51 51 51 57 48 48) }] }

theorem profile12_node29 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,5] 6 48 profile12_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,5] 6 48 profile12_node29_cert).mp (by decide +kernel))

def profile12_node30_cert : CutBound 6 := { lost := (rows 0 0 1 6 0 0), upper := (rows 19 7 38 25 52 36), lower := (rows 19 7 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 54 54 60 16 32) },{ target := 1, region := (rows 1 0 4 11 22 38), good := (rows 57 61 60 25 16 32) },{ target := 2, region := (rows 1 2 0 9 16 32), good := (rows 27 11 34 25 16 32) }] }

theorem profile12_node30 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,17] 6 36 profile12_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,17] 6 36 profile12_node30_cert).mp (by decide +kernel))

def profile12_node31_cert : CutBound 6 := { lost := (rows 4 16 16 2 0 0), upper := (rows 19 7 38 28 49 33), lower := (rows 19 7 38 28 16 32), losses := [{ target := 1, region := (rows 1 0 4 14 19 35), good := (rows 57 61 60 28 16 32) },{ target := 2, region := (rows 7 2 0 8 31 47), good := (rows 51 51 51 57 16 32) },{ target := 4, region := (rows 1 3 7 8 0 35), good := (rows 39 39 38 12 0 32) }] }

theorem profile12_node31 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,20] 6 33 profile12_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,20] 6 33 profile12_node31_cert).mp (by decide +kernel))

def profile12_node32_cert : CutBound 6 := { lost := (rows 0 16 17 2 0 0), upper := (rows 19 7 38 41 20 52), lower := (rows 19 7 38 41 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 54 54 60 16 32) },{ target := 1, region := (rows 1 0 4 11 22 38), good := (rows 57 61 60 41 16 32) },{ target := 4, region := (rows 1 10 12 8 0 32), good := (rows 3 7 38 47 0 32) }] }

theorem profile12_node32 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,33] 6 20 profile12_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,33] 6 20 profile12_node32_cert).mp (by decide +kernel))

def profile12_node33_cert : CutBound 6 := { lost := (rows 4 0 0 3 0 0), upper := (rows 19 7 38 44 17 49), lower := (rows 19 7 38 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 18 14 46 44 16 32) },{ target := 1, region := (rows 1 0 4 14 19 35), good := (rows 57 61 60 44 16 32) },{ target := 2, region := (rows 7 2 0 8 31 47), good := (rows 51 51 51 57 16 32) }] }

theorem profile12_node33 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,36] 6 17 profile12_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,36] 6 17 profile12_node33_cert).mp (by decide +kernel))

def profile12_node34_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 19 7 38 56 21 37), lower := (rows 19 7 38 56 16 32), losses := [{ target := 1, region := (rows 1 0 4 15 18 34), good := (rows 57 61 60 56 16 32) },{ target := 4, region := (rows 1 3 7 8 0 35), good := (rows 39 39 38 40 0 32) }] }

theorem profile12_node34 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,48] 6 5 profile12_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34,48] 6 5 profile12_node34_cert).mp (by decide +kernel))

def profile12_node28_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | _ => 0

def profile12_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node28 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,34] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile12_node28_route profile12_node28_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node29
  · exact profile12_node30
  · exact profile12_node31
  · exact profile12_node32
  · exact profile12_node33
  · exact profile12_node34

def profile12_node35_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 19 7 52 47 55 39), lower := (rows 19 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 43 47 36 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 19 7 23 8 16 0) }] }

theorem profile12_node35 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,48] 6 39 profile12_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5,48] 6 39 profile12_node35_cert).mp (by decide +kernel))

def profile12_node23_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node23_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node23 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile12_node23_route profile12_node23_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node24
  · exact profile12_node25
  · exact profile12_node26
  · exact profile12_node27
  · exact profile12_node28
  · exact profile12_node35

def profile12_node36_cert : CutBound 6 := { lost := (rows 4 4 16 16 0 0), upper := (rows 19 19 39 47 55 39), lower := (rows 19 19 4 8 16 32), losses := [{ target := 2, region := (rows 19 19 0 8 16 32), good := (rows 19 19 0 8 19 32) },{ target := 4, region := (rows 1 2 7 11 0 35), good := (rows 47 47 4 8 0 32) }] }

theorem profile12_node36 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,17] 6 39 profile12_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,17] 6 39 profile12_node36_cert).mp (by decide +kernel))

def profile12_node37_cert : CutBound 6 := { lost := (rows 4 0 16 16 0 0), upper := (rows 19 22 39 47 55 39), lower := (rows 19 22 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 32), good := (rows 19 19 0 8 16 32) },{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 6 4 8 0 32) }] }

theorem profile12_node37 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,20] 6 39 profile12_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,20] 6 39 profile12_node37_cert).mp (by decide +kernel))

def profile12_node39_cert : CutBound 6 := { lost := (rows 0 0 16 3 0 0), upper := (rows 19 35 7 60 52 52), lower := (rows 19 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 62 8 16 32) },{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 33 61 8 16 32) },{ target := 4, region := (rows 1 2 7 8 0 32), good := (rows 7 39 7 8 0 32) }] }

theorem profile12_node39 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,3] 6 52 profile12_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,3] 6 52 profile12_node39_cert).mp (by decide +kernel))

def profile12_node40_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 35 21 46 54 38), lower := (rows 19 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) },{ target := 4, region := (rows 1 6 4 12 0 36), good := (rows 3 35 47 8 0 32) }] }

theorem profile12_node40 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,17] 6 38 profile12_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,17] 6 38 profile12_node40_cert).mp (by decide +kernel))

def profile12_node41_cert : CutBound 6 := { lost := (rows 36 0 33 0 0 0), upper := (rows 19 35 22 45 53 37), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) },{ target := 2, region := (rows 5 2 0 8 16 32), good := (rows 19 35 19 8 16 32) },{ target := 5, region := (rows 5 2 5 8 16 0), good := (rows 23 7 23 8 16 0) }] }

theorem profile12_node41 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,18] 6 37 profile12_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,18] 6 37 profile12_node41_cert).mp (by decide +kernel))

def profile12_node42_cert : CutBound 6 := { lost := (rows 0 20 18 0 0 0), upper := (rows 19 35 37 30 22 54), lower := (rows 19 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) },{ target := 2, region := (rows 1 6 0 8 16 32), good := (rows 19 35 35 8 16 32) },{ target := 4, region := (rows 1 6 6 8 0 32), good := (rows 7 39 39 8 0 32) }] }

theorem profile12_node42 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,33] 6 22 profile12_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,33] 6 22 profile12_node42_cert).mp (by decide +kernel))

def profile12_node43_cert : CutBound 6 := { lost := (rows 32 0 17 32 0 0), upper := (rows 19 35 38 29 21 53), lower := (rows 19 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 22 38 38 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 7 39 38 8 0 32) },{ target := 5, region := (rows 5 2 4 12 20 0), good := (rows 19 3 31 8 16 0) }] }

theorem profile12_node43 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,34] 6 21 profile12_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,34] 6 21 profile12_node43_cert).mp (by decide +kernel))

def profile12_node45_cert : CutBound 6 := { lost := (rows 4 4 3 4 0 0), upper := (rows 19 35 52 11 20 36), lower := (rows 19 35 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 54 52 62 52 52) },{ target := 1, region := (rows 1 0 63 8 63 63), good := (rows 53 53 52 61 52 52) },{ target := 2, region := (rows 5 6 0 15 16 32), good := (rows 27 43 59 11 16 32) }] }

theorem profile12_node45 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,3] 6 4 profile12_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,3] 6 4 profile12_node45_cert).mp (by decide +kernel))

def profile12_node46_cert : CutBound 6 := { lost := (rows 4 4 1 0 0 0), upper := (rows 19 35 52 13 22 38), lower := (rows 19 35 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 54 52 60 16 32) },{ target := 2, region := (rows 5 6 0 8 16 32), good := (rows 19 35 51 11 16 32) }] }

theorem profile12_node46 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,5] 6 6 profile12_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,5] 6 6 profile12_node46_cert).mp (by decide +kernel))

def profile12_node47_cert : CutBound 6 := { lost := (rows 4 4 2 0 0 0), upper := (rows 19 35 52 14 21 37), lower := (rows 19 35 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 53 52 60 16 32) },{ target := 2, region := (rows 5 6 0 8 16 32), good := (rows 19 35 51 11 16 32) }] }

theorem profile12_node47 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,6] 6 5 profile12_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48,6] 6 5 profile12_node47_cert).mp (by decide +kernel))

def profile12_node44_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile12_node44_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node44 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33,48] 6 (by decide) (choices 2) [3,5,6] profile12_node44_route profile12_node44_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node45
  · exact profile12_node46
  · exact profile12_node47

def profile12_node38_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node38_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node38 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile12_node38_route profile12_node38_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node39
  · exact profile12_node40
  · exact profile12_node41
  · exact profile12_node42
  · exact profile12_node43
  · exact profile12_node44

def profile12_node49_cert : CutBound 6 := { lost := (rows 0 0 48 2 0 0), upper := (rows 19 38 7 61 53 53), lower := (rows 19 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 60 61 8 16 32) },{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 7 38 7 8 0 32) },{ target := 5, region := (rows 1 2 5 8 16 0), good := (rows 23 6 7 8 16 0) }] }

theorem profile12_node49 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,3] 6 53 profile12_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,3] 6 53 profile12_node49_cert).mp (by decide +kernel))

def profile12_node50_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 38 21 47 55 39), lower := (rows 19 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 36 21 8 16 32) },{ target := 4, region := (rows 1 6 4 12 0 36), good := (rows 3 46 47 8 0 32) }] }

theorem profile12_node50 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,17] 6 39 profile12_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,17] 6 39 profile12_node50_cert).mp (by decide +kernel))

def profile12_node51_cert : CutBound 6 := { lost := (rows 36 0 33 0 0 0), upper := (rows 19 38 22 45 53 37), lower := (rows 19 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) },{ target := 2, region := (rows 5 2 0 8 16 32), good := (rows 19 35 19 8 16 32) },{ target := 5, region := (rows 5 2 5 8 16 0), good := (rows 23 7 23 8 16 0) }] }

theorem profile12_node51 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,18] 6 37 profile12_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,18] 6 37 profile12_node51_cert).mp (by decide +kernel))

def profile12_node52_cert : CutBound 6 := { lost := (rows 32 17 0 32 0 0), upper := (rows 19 38 37 31 23 55), lower := (rows 19 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 38 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 38 39 8 0 32) },{ target := 5, region := (rows 3 2 4 10 18 0), good := (rows 27 31 5 8 16 0) }] }

theorem profile12_node52 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,33] 6 23 profile12_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,33] 6 23 profile12_node52_cert).mp (by decide +kernel))

def profile12_node53_cert : CutBound 6 := { lost := (rows 0 17 17 0 0 0), upper := (rows 19 38 38 29 21 53), lower := (rows 19 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 38 38 8 16 32), good := (rows 22 38 38 8 16 38) },{ target := 4, region := (rows 1 38 38 8 0 32), good := (rows 7 38 38 8 0 38) }] }

theorem profile12_node53 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,34] 6 21 profile12_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,34] 6 21 profile12_node53_cert).mp (by decide +kernel))

def profile12_node54_cert : CutBound 6 := { lost := (rows 32 17 0 32 0 0), upper := (rows 19 38 52 15 23 39), lower := (rows 19 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 54 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 38 38 8 0 32) },{ target := 5, region := (rows 3 2 4 10 18 0), good := (rows 27 31 20 8 16 0) }] }

theorem profile12_node54 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,48] 6 7 profile12_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36,48] 6 7 profile12_node54_cert).mp (by decide +kernel))

def profile12_node48_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node48 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,36] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile12_node48_route profile12_node48_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node49
  · exact profile12_node50
  · exact profile12_node51
  · exact profile12_node52
  · exact profile12_node53
  · exact profile12_node54

def profile12_node55_cert : CutBound 6 := { lost := (rows 4 0 16 16 0 0), upper := (rows 19 50 39 47 55 39), lower := (rows 19 50 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 32), good := (rows 19 51 0 8 16 32) },{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 34 4 8 0 32) }] }

theorem profile12_node55 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,48] 6 39 profile12_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18,48] 6 39 profile12_node55_cert).mp (by decide +kernel))

def profile12_node22_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node22 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile12_node22_route profile12_node22_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node23
  · exact profile12_node36
  · exact profile12_node37
  · exact profile12_node38
  · exact profile12_node48
  · exact profile12_node55

def profile12_node58_cert : CutBound 6 := { lost := (rows 0 16 16 1 0 0), upper := (rows 49 7 7 62 54 54), lower := (rows 49 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 48 62 62 8 16 32) },{ target := 4, region := (rows 1 7 7 8 0 32), good := (rows 39 7 7 8 0 32) }] }

theorem profile12_node58 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,3] 6 54 profile12_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,3] 6 54 profile12_node58_cert).mp (by decide +kernel))

def profile12_node59_cert : CutBound 6 := { lost := (rows 0 16 2 17 0 0), upper := (rows 49 7 21 46 54 38), lower := (rows 49 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 20 8 16 32) },{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 5 21 8 16 32) },{ target := 4, region := (rows 1 6 4 14 0 38), good := (rows 33 47 47 8 0 32) }] }

theorem profile12_node59 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,17] 6 38 profile12_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,17] 6 38 profile12_node59_cert).mp (by decide +kernel))

def profile12_node60_cert : CutBound 6 := { lost := (rows 0 32 32 16 0 0), upper := (rows 49 7 22 47 55 39), lower := (rows 49 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 46 8 0 32) },{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 7 22 8 16 0) }] }

theorem profile12_node60 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,18] 6 39 profile12_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,18] 6 39 profile12_node60_cert).mp (by decide +kernel))

def profile12_node61_cert : CutBound 6 := { lost := (rows 2 0 3 0 0 0), upper := (rows 49 7 52 15 23 39), lower := (rows 49 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 6 52 8 16 32) },{ target := 1, region := (rows 5 0 5 8 16 32), good := (rows 53 5 53 8 16 32) }] }

theorem profile12_node61 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,48] 6 7 profile12_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5,48] 6 7 profile12_node61_cert).mp (by decide +kernel))

def profile12_node57_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node57_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile12_node57 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,5] 6 (by decide) (choices 2) [3,17,18,48] profile12_node57_route profile12_node57_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node58
  · exact profile12_node59
  · exact profile12_node60
  · exact profile12_node61

def profile12_node62_cert : CutBound 6 := { lost := (rows 0 4 16 16 0 0), upper := (rows 49 19 39 47 55 39), lower := (rows 49 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 32), good := (rows 51 19 0 8 16 32) },{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 33 47 4 8 0 32) }] }

theorem profile12_node62 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,17] 6 39 profile12_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,17] 6 39 profile12_node62_cert).mp (by decide +kernel))

def profile12_node64_cert : CutBound 6 := { lost := (rows 0 32 32 16 0 0), upper := (rows 49 22 7 47 55 39), lower := (rows 49 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 33 46 47 8 0 32) },{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 22 7 8 16 0) }] }

theorem profile12_node64 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,3] 6 39 profile12_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,3] 6 39 profile12_node64_cert).mp (by decide +kernel))

def profile12_node65_cert : CutBound 6 := { lost := (rows 0 32 18 32 0 0), upper := (rows 49 22 37 15 23 39), lower := (rows 49 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 20 37 8 16 32) },{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 37 6 37 8 0 32) },{ target := 5, region := (rows 1 6 4 12 20 0), good := (rows 17 30 31 8 16 0) }] }

theorem profile12_node65 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,33] 6 7 profile12_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,33] 6 7 profile12_node65_cert).mp (by decide +kernel))

def profile12_node67_cert : CutBound 6 := { lost := (rows 2 1 1 0 0 0), upper := (rows 49 22 38 11 21 37), lower := (rows 49 22 38 11 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 14 16 32) },{ target := 1, region := (rows 15 0 4 8 22 38), good := (rows 49 53 53 57 16 32) }] }

theorem profile12_node67 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,3] 6 5 profile12_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,3] 6 5 profile12_node67_cert).mp (by decide +kernel))

def profile12_node68_cert : CutBound 6 := { lost := (rows 4 1 1 0 0 0), upper := (rows 49 22 38 13 19 35), lower := (rows 49 22 38 13 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 14 16 32) },{ target := 2, region := (rows 15 2 0 8 22 38), good := (rows 49 51 51 57 16 32) }] }

theorem profile12_node68 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,5] 6 3 profile12_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,5] 6 3 profile12_node68_cert).mp (by decide +kernel))

def profile12_node69_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 49 22 38 14 17 33), lower := (rows 49 22 38 14 16 32), losses := [{ target := 0, region := (rows 0 3 5 15 16 32), good := (rows 62 30 46 14 16 32) }] }

theorem profile12_node69 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,6] 6 1 profile12_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34,6] 6 1 profile12_node69_cert).mp (by decide +kernel))

def profile12_node66_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile12_node66_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node66 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20,34] 6 (by decide) (choices 2) [3,5,6] profile12_node66_route profile12_node66_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node67
  · exact profile12_node68
  · exact profile12_node69

def profile12_node63_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile12_node63_route : Route 6 := (fun mask => (mask,id))

theorem profile12_node63 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,20] 6 (by decide) (choices 2) [3,33,34] profile12_node63_route profile12_node63_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node64
  · exact profile12_node65
  · exact profile12_node66

def profile12_node70_cert : CutBound 6 := { lost := (rows 6 5 0 0 0 0), upper := (rows 49 50 7 15 23 39), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) },{ target := 1, region := (rows 3 0 4 8 16 32), good := (rows 49 49 4 8 16 32) },{ target := 2, region := (rows 3 3 0 8 16 32), good := (rows 51 51 0 8 16 32) }] }

theorem profile12_node70 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,48] 6 7 profile12_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48,48] 6 7 profile12_node70_cert).mp (by decide +kernel))

def profile12_node56_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node56_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile12_node56 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [48] 6 (by decide) (choices 2) [5,17,20,48] profile12_node56_route profile12_node56_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node57
  · exact profile12_node62
  · exact profile12_node63
  · exact profile12_node70

def profile12_node0_column : Nat → Fin 6 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile12_node0_route : Route 6 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile12_node0 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [] 6 (by decide) (choices 2) [6,18,48] profile12_node0_route profile12_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node1
  · exact profile12_node22
  · exact profile12_node56

theorem profile12 : Upper (D (n:=6) [34,34,34,32,18,18]) (R (n:=6) [34,34,34,32,18,18]) [] 6 := profile12_node0


#print axioms profile12
end Delivery.SmallBudgetTenFinite6
