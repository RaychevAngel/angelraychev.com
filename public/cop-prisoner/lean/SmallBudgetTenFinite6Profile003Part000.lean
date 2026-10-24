import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile3_node3_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 15 19 7 56 48 32), lower := (rows 15 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) }] }

theorem profile3_node3 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,3] 6 48 profile3_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,3] 6 48 profile3_node3_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 15 19 21 42 50 32), lower := (rows 15 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node4 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,17] 6 34 profile3_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,17] 6 34 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 15 19 22 41 49 32), lower := (rows 15 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 46 54 54 40 48 32) }] }

theorem profile3_node5 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,18] 6 33 profile3_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,18] 6 33 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 15 19 37 58 50 32), lower := (rows 15 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node6 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,33] 6 50 profile3_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,33] 6 50 profile3_node6_cert).mp (by decide +kernel))

def profile3_node7_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 15 19 38 57 49 32), lower := (rows 15 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 46 54 38 40 48 32) }] }

theorem profile3_node7 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,34] 6 49 profile3_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,34] 6 49 profile3_node7_cert).mp (by decide +kernel))

def profile3_node8_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 15 19 52 43 51 32), lower := (rows 15 19 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 22 8 16 63), good := (rows 46 54 52 40 52 32) }] }

theorem profile3_node8 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,48] 6 35 profile3_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17,48] 6 35 profile3_node8_cert).mp (by decide +kernel))

def profile3_node2_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node2 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node2_route profile3_node2_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node3
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6
  · exact profile3_node7
  · exact profile3_node8

def profile3_node9_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 15 35 55 59 51 32), lower := (rows 15 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 47 35 36 40 32 32) }] }

theorem profile3_node9 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,33] 6 51 profile3_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,33] 6 51 profile3_node9_cert).mp (by decide +kernel))

def profile3_node10_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 15 50 55 59 51 32), lower := (rows 15 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 46 50 36 40 50 32) }] }

theorem profile3_node10 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,48] 6 51 profile3_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14,48] 6 51 profile3_node10_cert).mp (by decide +kernel))

def profile3_node1_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [14] 6 (by decide) (choices 2) [17,33,48] profile3_node1_route profile3_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node9
  · exact profile3_node10

def profile3_node13_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 23 11 7 56 48 32), lower := (rows 23 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) }] }

theorem profile3_node13 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,3] 6 48 profile3_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,3] 6 48 profile3_node13_cert).mp (by decide +kernel))

def profile3_node14_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 23 11 21 42 50 32), lower := (rows 23 11 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node14 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,17] 6 34 profile3_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,17] 6 34 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 23 11 22 41 49 32), lower := (rows 23 11 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 63), good := (rows 54 46 54 40 48 32) }] }

theorem profile3_node15 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,18] 6 33 profile3_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,18] 6 33 profile3_node15_cert).mp (by decide +kernel))

def profile3_node16_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 23 11 37 58 50 32), lower := (rows 23 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node16 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,33] 6 50 profile3_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,33] 6 50 profile3_node16_cert).mp (by decide +kernel))

def profile3_node17_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 23 11 38 57 49 32), lower := (rows 23 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 54 46 38 40 48 32) }] }

theorem profile3_node17 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,34] 6 49 profile3_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,34] 6 49 profile3_node17_cert).mp (by decide +kernel))

def profile3_node18_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 23 11 52 43 51 32), lower := (rows 23 11 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 21 8 16 63), good := (rows 54 46 52 40 52 32) }] }

theorem profile3_node18 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,48] 6 35 profile3_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9,48] 6 35 profile3_node18_cert).mp (by decide +kernel))

def profile3_node12_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node12_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node12 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node12_route profile3_node12_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node13
  · exact profile3_node14
  · exact profile3_node15
  · exact profile3_node16
  · exact profile3_node17
  · exact profile3_node18

def profile3_node19_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 23 19 47 43 59 32), lower := (rows 23 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 63), good := (rows 47 47 36 40 32 32) }] }

theorem profile3_node19 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,17] 6 43 profile3_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,17] 6 43 profile3_node19_cert).mp (by decide +kernel))

def profile3_node20_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 23 26 39 43 51 32), lower := (rows 23 26 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 63), good := (rows 47 42 36 40 32 32) }] }

theorem profile3_node20 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,24] 6 35 profile3_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,24] 6 35 profile3_node20_cert).mp (by decide +kernel))

def profile3_node21_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 23 35 63 59 59 32), lower := (rows 23 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 39 35 36 40 32 32) }] }

theorem profile3_node21 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,33] 6 59 profile3_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,33] 6 59 profile3_node21_cert).mp (by decide +kernel))

def profile3_node22_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 23 42 55 59 51 32), lower := (rows 23 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 54 42 36 42 48 32) }] }

theorem profile3_node22 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,40] 6 51 profile3_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,40] 6 51 profile3_node22_cert).mp (by decide +kernel))

def profile3_node23_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 23 50 47 43 59 32), lower := (rows 23 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 54 50 36 40 50 32) }] }

theorem profile3_node23 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,48] 6 43 profile3_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22,48] 6 43 profile3_node23_cert).mp (by decide +kernel))

def profile3_node11_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile3_node11_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node11 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [22] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node11_route profile3_node11_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node12
  · exact profile3_node19
  · exact profile3_node20
  · exact profile3_node21
  · exact profile3_node22
  · exact profile3_node23

def profile3_node25_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 29 19 39 43 51 32), lower := (rows 29 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 63), good := (rows 45 47 36 40 32 32) }] }

theorem profile3_node25 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,17] 6 35 profile3_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,17] 6 35 profile3_node25_cert).mp (by decide +kernel))

def profile3_node26_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 29 35 55 59 51 32), lower := (rows 29 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 47 35 36 40 32 32) }] }

theorem profile3_node26 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,33] 6 51 profile3_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,33] 6 51 profile3_node26_cert).mp (by decide +kernel))

def profile3_node27_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 29 50 39 43 51 32), lower := (rows 29 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 62 50 36 40 50 32) }] }

theorem profile3_node27 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,48] 6 35 profile3_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28,48] 6 35 profile3_node27_cert).mp (by decide +kernel))

def profile3_node24_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node24_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node24 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [28] 6 (by decide) (choices 2) [17,33,48] profile3_node24_route profile3_node24_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node25
  · exact profile3_node26
  · exact profile3_node27

def profile3_node30_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 11 7 56 48 32), lower := (rows 39 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) }] }

theorem profile3_node30 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,3] 6 48 profile3_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,3] 6 48 profile3_node30_cert).mp (by decide +kernel))

def profile3_node31_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 11 21 58 50 32), lower := (rows 39 11 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node31 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,17] 6 50 profile3_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,17] 6 50 profile3_node31_cert).mp (by decide +kernel))

def profile3_node32_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 11 22 57 49 32), lower := (rows 39 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile3_node32 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,18] 6 49 profile3_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,18] 6 49 profile3_node32_cert).mp (by decide +kernel))

def profile3_node33_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 11 37 26 18 32), lower := (rows 39 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node33 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,33] 6 18 profile3_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,33] 6 18 profile3_node33_cert).mp (by decide +kernel))

def profile3_node34_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 11 38 25 17 32), lower := (rows 39 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 46 38 40 48 32) }] }

theorem profile3_node34 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,34] 6 17 profile3_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,34] 6 17 profile3_node34_cert).mp (by decide +kernel))

def profile3_node35_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 11 52 27 19 32), lower := (rows 39 11 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 20 8 16 63), good := (rows 38 42 52 40 52 32) }] }

theorem profile3_node35 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,48] 6 19 profile3_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9,48] 6 19 profile3_node35_cert).mp (by decide +kernel))

def profile3_node29_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node29_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node29 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node29_route profile3_node29_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node30
  · exact profile3_node31
  · exact profile3_node32
  · exact profile3_node33
  · exact profile3_node34
  · exact profile3_node35

def profile3_node37_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 19 7 56 56 32), lower := (rows 39 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) }] }

theorem profile3_node37 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,3] 6 56 profile3_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,3] 6 56 profile3_node37_cert).mp (by decide +kernel))

def profile3_node38_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 19 13 58 50 32), lower := (rows 39 19 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node38 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,9] 6 50 profile3_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,9] 6 50 profile3_node38_cert).mp (by decide +kernel))

def profile3_node39_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 19 14 57 49 32), lower := (rows 39 19 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 63), good := (rows 61 57 60 40 48 32) }] }

theorem profile3_node39 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,10] 6 49 profile3_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,10] 6 49 profile3_node39_cert).mp (by decide +kernel))

def profile3_node40_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 19 21 42 58 32), lower := (rows 39 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node40 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,17] 6 42 profile3_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,17] 6 42 profile3_node40_cert).mp (by decide +kernel))

def profile3_node41_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 19 22 41 57 32), lower := (rows 39 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 38 54 54 40 48 32) }] }

theorem profile3_node41 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,18] 6 41 profile3_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,18] 6 41 profile3_node41_cert).mp (by decide +kernel))

def profile3_node42_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 39 19 28 43 51 32), lower := (rows 39 19 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 63), good := (rows 47 43 44 40 32 32) }] }

theorem profile3_node42 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,24] 6 35 profile3_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,24] 6 35 profile3_node42_cert).mp (by decide +kernel))

def profile3_node43_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 39 19 37 26 26 32), lower := (rows 39 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 62 58 60 40 48 32) }] }

theorem profile3_node43 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,33] 6 26 profile3_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,33] 6 26 profile3_node43_cert).mp (by decide +kernel))

def profile3_node44_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 19 38 25 25 32), lower := (rows 39 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 54 38 40 48 32) }] }

theorem profile3_node44 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,34] 6 25 profile3_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,34] 6 25 profile3_node44_cert).mp (by decide +kernel))

def profile3_node45_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 19 44 27 19 32), lower := (rows 39 19 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 38 50 44 44 48 32) }] }

theorem profile3_node45 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,40] 6 19 profile3_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,40] 6 19 profile3_node45_cert).mp (by decide +kernel))

def profile3_node46_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 19 52 11 27 32), lower := (rows 39 19 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 22 8 16 63), good := (rows 38 54 52 40 52 32) }] }

theorem profile3_node46 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,48] 6 11 profile3_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17,48] 6 11 profile3_node46_cert).mp (by decide +kernel))

def profile3_node36_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile3_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node36 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,17] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile3_node36_route profile3_node36_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node37
  · exact profile3_node38
  · exact profile3_node39
  · exact profile3_node40
  · exact profile3_node41
  · exact profile3_node42
  · exact profile3_node43
  · exact profile3_node44
  · exact profile3_node45
  · exact profile3_node46

def profile3_node48_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 39 26 7 57 49 32), lower := (rows 39 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 61 56 61 40 48 32) }] }

theorem profile3_node48 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,3] 6 49 profile3_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,3] 6 49 profile3_node48_cert).mp (by decide +kernel))

def profile3_node49_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 39 26 21 43 51 32), lower := (rows 39 26 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 63), good := (rows 47 42 45 40 32 32) }] }

theorem profile3_node49 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,17] 6 35 profile3_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,17] 6 35 profile3_node49_cert).mp (by decide +kernel))

def profile3_node50_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 26 22 41 49 32), lower := (rows 39 26 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 38 62 54 40 48 32) }] }

theorem profile3_node50 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,18] 6 33 profile3_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,18] 6 33 profile3_node50_cert).mp (by decide +kernel))

def profile3_node51_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 39 26 37 27 19 32), lower := (rows 39 26 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 56 37 40 48 32) }] }

theorem profile3_node51 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,33] 6 19 profile3_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,33] 6 19 profile3_node51_cert).mp (by decide +kernel))

def profile3_node52_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 26 38 25 17 32), lower := (rows 39 26 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 62 38 40 48 32) }] }

theorem profile3_node52 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,34] 6 17 profile3_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,34] 6 17 profile3_node52_cert).mp (by decide +kernel))

def profile3_node53_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 39 26 52 11 19 32), lower := (rows 39 26 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 22 8 16 63), good := (rows 38 62 52 40 52 32) }] }

theorem profile3_node53 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,48] 6 3 profile3_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24,48] 6 3 profile3_node53_cert).mp (by decide +kernel))

def profile3_node47_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node47_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node47 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,24] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node47_route profile3_node47_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node48
  · exact profile3_node49
  · exact profile3_node50
  · exact profile3_node51
  · exact profile3_node52
  · exact profile3_node53

def profile3_node54_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 39 35 31 27 27 32), lower := (rows 39 35 4 8 16 32), losses := [{ target := 4, region := (rows 5 7 4 8 0 63), good := (rows 39 35 39 40 32 32) }] }

theorem profile3_node54 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,33] 6 27 profile3_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,33] 6 27 profile3_node54_cert).mp (by decide +kernel))

def profile3_node55_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 39 42 23 27 19 32), lower := (rows 39 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 38 42 36 42 48 32) }] }

theorem profile3_node55 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,40] 6 19 profile3_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,40] 6 19 profile3_node55_cert).mp (by decide +kernel))

def profile3_node56_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 39 50 31 27 27 32), lower := (rows 39 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 38 50 36 40 50 32) }] }

theorem profile3_node56 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,48] 6 27 profile3_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38,48] 6 27 profile3_node56_cert).mp (by decide +kernel))

def profile3_node28_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile3_node28_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node28 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [38] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node28_route profile3_node28_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node29
  · exact profile3_node36
  · exact profile3_node47
  · exact profile3_node54
  · exact profile3_node55
  · exact profile3_node56

def profile3_node59_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 45 19 7 58 50 32), lower := (rows 45 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 60 58 62 40 48 32) }] }

theorem profile3_node59 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,3] 6 50 profile3_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,3] 6 50 profile3_node59_cert).mp (by decide +kernel))

def profile3_node60_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 45 19 21 42 50 32), lower := (rows 45 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 44 58 52 40 48 32) }] }

theorem profile3_node60 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,17] 6 34 profile3_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,17] 6 34 profile3_node60_cert).mp (by decide +kernel))

def profile3_node61_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 45 19 22 43 51 32), lower := (rows 45 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 44 54 54 40 48 32) }] }

theorem profile3_node61 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,18] 6 35 profile3_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,18] 6 35 profile3_node61_cert).mp (by decide +kernel))

def profile3_node62_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 45 19 37 26 18 32), lower := (rows 45 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 44 58 36 40 48 32) }] }

theorem profile3_node62 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,33] 6 18 profile3_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,33] 6 18 profile3_node62_cert).mp (by decide +kernel))

def profile3_node63_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 45 19 38 27 19 32), lower := (rows 45 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 44 54 38 40 48 32) }] }

theorem profile3_node63 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,34] 6 19 profile3_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,34] 6 19 profile3_node63_cert).mp (by decide +kernel))

def profile3_node64_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 45 19 52 11 19 32), lower := (rows 45 19 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 22 8 16 63), good := (rows 44 54 52 40 52 32) }] }

theorem profile3_node64 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,48] 6 3 profile3_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17,48] 6 3 profile3_node64_cert).mp (by decide +kernel))

def profile3_node58_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node58_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node58 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node58_route profile3_node58_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node59
  · exact profile3_node60
  · exact profile3_node61
  · exact profile3_node62
  · exact profile3_node63
  · exact profile3_node64

def profile3_node65_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 45 35 23 27 19 32), lower := (rows 45 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 47 35 36 40 32 32) }] }

theorem profile3_node65 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,33] 6 19 profile3_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,33] 6 19 profile3_node65_cert).mp (by decide +kernel))

def profile3_node66_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 45 50 23 27 19 32), lower := (rows 45 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 44 50 36 40 50 32) }] }

theorem profile3_node66 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,48] 6 19 profile3_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44,48] 6 19 profile3_node66_cert).mp (by decide +kernel))

def profile3_node57_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node57_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node57 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [44] 6 (by decide) (choices 2) [17,33,48] profile3_node57_route profile3_node57_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node58
  · exact profile3_node65
  · exact profile3_node66

def profile3_node69_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 51 7 7 56 56 32), lower := (rows 51 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 62 62 56 56 56) }] }

theorem profile3_node69 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,3] 6 56 profile3_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,3] 6 56 profile3_node69_cert).mp (by decide +kernel))

def profile3_node70_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 51 7 13 58 50 32), lower := (rows 51 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 58 62 60 40 48 32) }] }

theorem profile3_node70 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,9] 6 50 profile3_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,9] 6 50 profile3_node70_cert).mp (by decide +kernel))

def profile3_node71_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 7 14 57 49 32), lower := (rows 51 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile3_node71 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,10] 6 49 profile3_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,10] 6 49 profile3_node71_cert).mp (by decide +kernel))

def profile3_node72_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 51 7 21 42 58 32), lower := (rows 51 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 58 62 60 40 48 32) }] }

theorem profile3_node72 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,17] 6 42 profile3_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,17] 6 42 profile3_node72_cert).mp (by decide +kernel))

def profile3_node73_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 7 22 41 57 32), lower := (rows 51 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 63), good := (rows 54 38 54 40 48 32) }] }

theorem profile3_node73 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,18] 6 41 profile3_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,18] 6 41 profile3_node73_cert).mp (by decide +kernel))

def profile3_node74_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 51 7 28 43 51 32), lower := (rows 51 7 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 63), good := (rows 43 47 44 40 32 32) }] }

theorem profile3_node74 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,24] 6 35 profile3_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,24] 6 35 profile3_node74_cert).mp (by decide +kernel))

def profile3_node75_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 51 7 37 26 26 32), lower := (rows 51 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 63), good := (rows 58 62 60 40 48 32) }] }

theorem profile3_node75 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,33] 6 26 profile3_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,33] 6 26 profile3_node75_cert).mp (by decide +kernel))

def profile3_node76_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 7 38 25 25 32), lower := (rows 51 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 54 38 38 40 48 32) }] }

theorem profile3_node76 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,34] 6 25 profile3_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,34] 6 25 profile3_node76_cert).mp (by decide +kernel))

def profile3_node77_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 7 44 27 19 32), lower := (rows 51 7 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 50 38 44 44 48 32) }] }

theorem profile3_node77 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,40] 6 19 profile3_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,40] 6 19 profile3_node77_cert).mp (by decide +kernel))

def profile3_node78_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 7 52 11 27 32), lower := (rows 51 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 21 8 16 63), good := (rows 54 38 52 40 52 32) }] }

theorem profile3_node78 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,48] 6 11 profile3_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5,48] 6 11 profile3_node78_cert).mp (by decide +kernel))

def profile3_node68_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile3_node68_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node68 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile3_node68_route profile3_node68_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node69
  · exact profile3_node70
  · exact profile3_node71
  · exact profile3_node72
  · exact profile3_node73
  · exact profile3_node74
  · exact profile3_node75
  · exact profile3_node76
  · exact profile3_node77
  · exact profile3_node78

def profile3_node80_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 51 14 7 57 49 32), lower := (rows 51 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 63), good := (rows 57 60 61 40 48 32) }] }

theorem profile3_node80 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,3] 6 49 profile3_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,3] 6 49 profile3_node80_cert).mp (by decide +kernel))

def profile3_node81_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 14 21 43 51 32), lower := (rows 51 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 53 44 53 40 48 32) }] }

theorem profile3_node81 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,17] 6 35 profile3_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,17] 6 35 profile3_node81_cert).mp (by decide +kernel))

def profile3_node82_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 14 22 41 49 32), lower := (rows 51 14 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 63), good := (rows 54 46 54 40 48 32) }] }

theorem profile3_node82 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,18] 6 33 profile3_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,18] 6 33 profile3_node82_cert).mp (by decide +kernel))

def profile3_node83_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 51 14 37 27 19 32), lower := (rows 51 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 53 44 37 40 48 32) }] }

theorem profile3_node83 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,33] 6 19 profile3_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,33] 6 19 profile3_node83_cert).mp (by decide +kernel))

def profile3_node84_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 51 14 38 25 17 32), lower := (rows 51 14 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 54 46 38 46 48 32) }] }

theorem profile3_node84 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,34] 6 17 profile3_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,34] 6 17 profile3_node84_cert).mp (by decide +kernel))

def profile3_node85_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 51 14 52 11 19 32), lower := (rows 51 14 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 21 8 16 63), good := (rows 54 46 52 40 52 32) }] }

theorem profile3_node85 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,48] 6 3 profile3_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12,48] 6 3 profile3_node85_cert).mp (by decide +kernel))

def profile3_node79_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node79_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node79 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,12] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node79_route profile3_node79_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node80
  · exact profile3_node81
  · exact profile3_node82
  · exact profile3_node83
  · exact profile3_node84
  · exact profile3_node85

def profile3_node86_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 51 19 47 47 63 32), lower := (rows 51 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 63), good := (rows 47 47 36 40 32 32) }] }

theorem profile3_node86 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,17] 6 47 profile3_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,17] 6 47 profile3_node86_cert).mp (by decide +kernel))

def profile3_node87_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 51 22 47 43 59 32), lower := (rows 51 22 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 63), good := (rows 47 38 36 40 32 32) }] }

theorem profile3_node87 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,20] 6 43 profile3_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,20] 6 43 profile3_node87_cert).mp (by decide +kernel))

def profile3_node88_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 51 35 31 31 31 32), lower := (rows 51 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 35 35 36 40 32 32) }] }

theorem profile3_node88 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,33] 6 31 profile3_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,33] 6 31 profile3_node88_cert).mp (by decide +kernel))

def profile3_node89_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 51 38 31 27 27 32), lower := (rows 51 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 50 38 38 40 48 32) }] }

theorem profile3_node89 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,36] 6 27 profile3_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,36] 6 27 profile3_node89_cert).mp (by decide +kernel))

def profile3_node90_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 51 50 15 15 31 32), lower := (rows 51 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 50 50 36 40 50 32) }] }

theorem profile3_node90 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,48] 6 15 profile3_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50,48] 6 15 profile3_node90_cert).mp (by decide +kernel))

def profile3_node67_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile3_node67_route : Route 6 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile3_node67 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [50] 6 (by decide) (choices 2) [5,12,17,20,33,36,48] profile3_node67_route profile3_node67_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node68
  · exact profile3_node79
  · exact profile3_node86
  · exact profile3_node87
  · exact profile3_node88
  · exact profile3_node89
  · exact profile3_node90

def profile3_node93_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 53 11 7 58 50 32), lower := (rows 53 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 60 58 62 40 48 32) }] }

theorem profile3_node93 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,3] 6 50 profile3_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,3] 6 50 profile3_node93_cert).mp (by decide +kernel))

def profile3_node94_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 53 11 21 42 50 32), lower := (rows 53 11 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 52 58 52 40 48 32) }] }

theorem profile3_node94 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,17] 6 34 profile3_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,17] 6 34 profile3_node94_cert).mp (by decide +kernel))

def profile3_node95_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 53 11 22 43 51 32), lower := (rows 53 11 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 63), good := (rows 53 41 53 40 48 32) }] }

theorem profile3_node95 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,18] 6 35 profile3_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,18] 6 35 profile3_node95_cert).mp (by decide +kernel))

def profile3_node96_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 53 11 37 26 18 32), lower := (rows 53 11 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 52 58 36 40 48 32) }] }

theorem profile3_node96 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,33] 6 18 profile3_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,33] 6 18 profile3_node96_cert).mp (by decide +kernel))

def profile3_node97_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 53 11 38 27 19 32), lower := (rows 53 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 52 46 38 40 48 32) }] }

theorem profile3_node97 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,34] 6 19 profile3_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,34] 6 19 profile3_node97_cert).mp (by decide +kernel))

def profile3_node98_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 53 11 52 11 19 32), lower := (rows 53 11 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 21 8 16 63), good := (rows 52 46 52 40 52 32) }] }

theorem profile3_node98 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,48] 6 3 profile3_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9,48] 6 3 profile3_node98_cert).mp (by decide +kernel))

def profile3_node92_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile3_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node92 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile3_node92_route profile3_node92_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node93
  · exact profile3_node94
  · exact profile3_node95
  · exact profile3_node96
  · exact profile3_node97
  · exact profile3_node98

def profile3_node99_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 53 19 47 43 59 32), lower := (rows 53 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 63), good := (rows 37 47 36 40 32 32) }] }

theorem profile3_node99 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,17] 6 43 profile3_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,17] 6 43 profile3_node99_cert).mp (by decide +kernel))

def profile3_node101_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 53 26 7 43 51 32), lower := (rows 53 26 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 63), good := (rows 45 42 47 40 32 32) }] }

theorem profile3_node101 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,3] 6 35 profile3_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,3] 6 35 profile3_node101_cert).mp (by decide +kernel))

def profile3_node102_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 53 26 37 11 19 32), lower := (rows 53 26 37 8 16 32), losses := [{ target := 1, region := (rows 19 0 23 8 16 63), good := (rows 53 61 37 40 53 32) }] }

theorem profile3_node102 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,33] 6 3 profile3_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,33] 6 3 profile3_node102_cert).mp (by decide +kernel))

def profile3_node103_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 53 26 38 11 19 32), lower := (rows 53 26 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 52 62 38 40 48 32) }] }

theorem profile3_node103 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,34] 6 3 profile3_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24,34] 6 3 profile3_node103_cert).mp (by decide +kernel))

def profile3_node100_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile3_node100_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node100 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,24] 6 (by decide) (choices 2) [3,33,34] profile3_node100_route profile3_node100_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node101
  · exact profile3_node102
  · exact profile3_node103

def profile3_node104_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 53 35 31 27 27 32), lower := (rows 53 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 63), good := (rows 39 35 36 40 32 32) }] }

theorem profile3_node104 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,33] 6 27 profile3_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,33] 6 27 profile3_node104_cert).mp (by decide +kernel))

def profile3_node105_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 53 42 23 27 19 32), lower := (rows 53 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 52 42 36 42 48 32) }] }

theorem profile3_node105 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,40] 6 19 profile3_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,40] 6 19 profile3_node105_cert).mp (by decide +kernel))

def profile3_node106_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 53 50 15 11 27 32), lower := (rows 53 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 19 4 8 16 63), good := (rows 54 50 36 40 50 32) }] }

theorem profile3_node106 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,48] 6 11 profile3_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52,48] 6 11 profile3_node106_cert).mp (by decide +kernel))

def profile3_node91_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile3_node91_route : Route 6 := (fun mask => (mask,id))

theorem profile3_node91 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [52] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile3_node91_route profile3_node91_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node92
  · exact profile3_node99
  · exact profile3_node100
  · exact profile3_node104
  · exact profile3_node105
  · exact profile3_node106

def profile3_node0_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile3_node0_route : Route 6 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 42 => (38,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 56 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [] 6 (by decide) (choices 3) [14,22,28,38,44,50,52] profile3_node0_route profile3_node0_column
    (by change RowCover 6 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node11
  · exact profile3_node24
  · exact profile3_node28
  · exact profile3_node57
  · exact profile3_node67
  · exact profile3_node91

theorem profile3 : Upper (D (n:=6) [50,34,33,33,18,2]) (R (n:=6) [50,34,33,33,18,2]) [] 6 := profile3_node0


#print axioms profile3
end Delivery.SmallBudgetTenFinite6
