import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile14_node3_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 7 56 48 48), lower := (rows 7 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) }] }

theorem profile14_node3 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,3] 6 48 profile14_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,3] 6 48 profile14_node3_cert).mp (by decide +kernel))

def profile14_node4_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 21 58 50 50), lower := (rows 7 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 62 58 60 8 16 32) }] }

theorem profile14_node4 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,17] 6 50 profile14_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,17] 6 50 profile14_node4_cert).mp (by decide +kernel))

def profile14_node5_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 22 57 49 49), lower := (rows 7 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 22 22 8 16 32) }] }

theorem profile14_node5 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,18] 6 49 profile14_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,18] 6 49 profile14_node5_cert).mp (by decide +kernel))

def profile14_node6_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 37 58 50 50), lower := (rows 7 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 62 58 60 8 16 32) }] }

theorem profile14_node6 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,33] 6 50 profile14_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,33] 6 50 profile14_node6_cert).mp (by decide +kernel))

def profile14_node7_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 38 57 49 49), lower := (rows 7 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) }] }

theorem profile14_node7 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,34] 6 49 profile14_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,34] 6 49 profile14_node7_cert).mp (by decide +kernel))

def profile14_node8_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 7 19 52 59 51 51), lower := (rows 7 19 52 8 16 32), losses := [{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 7 19 23 8 16 0) }] }

theorem profile14_node8 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,48] 6 51 profile14_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17,48] 6 51 profile14_node8_cert).mp (by decide +kernel))

def profile14_node2_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node2 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node2_route profile14_node2_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node3
  · exact profile14_node4
  · exact profile14_node5
  · exact profile14_node6
  · exact profile14_node7
  · exact profile14_node8

def profile14_node10_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 35 21 58 50 50), lower := (rows 7 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 62 58 60 8 16 32) }] }

theorem profile14_node10 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,17] 6 50 profile14_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,17] 6 50 profile14_node10_cert).mp (by decide +kernel))

def profile14_node11_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 35 22 57 49 49), lower := (rows 7 35 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) }] }

theorem profile14_node11 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,18] 6 49 profile14_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,18] 6 49 profile14_node11_cert).mp (by decide +kernel))

def profile14_node12_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 7 35 52 27 19 51), lower := (rows 7 35 52 8 16 32), losses := [{ target := 4, region := (rows 5 6 4 8 0 32), good := (rows 7 35 39 8 0 32) }] }

theorem profile14_node12 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,48] 6 19 profile14_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33,48] 6 19 profile14_node12_cert).mp (by decide +kernel))

def profile14_node9_column : Nat → Fin 6 := fun mask => match mask with | 3 => 4 | 9 => 3 | 33 => 4 | 10 => 3 | 34 => 4 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node9_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node9 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,33] 6 (by decide) (choices 2) [17,18,48] profile14_node9_route profile14_node9_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node10
  · exact profile14_node11
  · exact profile14_node12

def profile14_node14_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 50 7 57 49 49), lower := (rows 7 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 48 61 8 16 32) }] }

theorem profile14_node14 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,3] 6 49 profile14_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,3] 6 49 profile14_node14_cert).mp (by decide +kernel))

def profile14_node15_cert : CutBound 6 := { lost := (rows 32 0 32 0 0 0), upper := (rows 7 50 21 59 51 51), lower := (rows 7 50 21 8 16 32), losses := [{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 7 23 21 8 16 0) }] }

theorem profile14_node15 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,17] 6 51 profile14_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,17] 6 51 profile14_node15_cert).mp (by decide +kernel))

def profile14_node16_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 50 22 57 49 49), lower := (rows 7 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 22 8 16 32) }] }

theorem profile14_node16 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,18] 6 49 profile14_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,18] 6 49 profile14_node16_cert).mp (by decide +kernel))

def profile14_node17_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 7 50 37 27 19 51), lower := (rows 7 50 37 8 16 32), losses := [{ target := 4, region := (rows 3 2 6 8 0 32), good := (rows 7 39 37 8 0 32) }] }

theorem profile14_node17 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,33] 6 19 profile14_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,33] 6 19 profile14_node17_cert).mp (by decide +kernel))

def profile14_node18_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 50 38 25 17 49), lower := (rows 7 50 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 38 8 16 32) }] }

theorem profile14_node18 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,34] 6 17 profile14_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,34] 6 17 profile14_node18_cert).mp (by decide +kernel))

def profile14_node19_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 7 50 52 27 19 51), lower := (rows 7 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 6 54 54 8 16 32) }] }

theorem profile14_node19 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,48] 6 19 profile14_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48,48] 6 19 profile14_node19_cert).mp (by decide +kernel))

def profile14_node13_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node13 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6,48] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node13_route profile14_node13_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node14
  · exact profile14_node15
  · exact profile14_node16
  · exact profile14_node17
  · exact profile14_node18
  · exact profile14_node19

def profile14_node1_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node1_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [6] 6 (by decide) (choices 2) [17,33,48] profile14_node1_route profile14_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node9
  · exact profile14_node13

def profile14_node22_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 7 56 48 48), lower := (rows 19 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 62 62 56 56 56) }] }

theorem profile14_node22 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,3] 6 48 profile14_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,3] 6 48 profile14_node22_cert).mp (by decide +kernel))

def profile14_node23_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 21 58 50 50), lower := (rows 19 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) }] }

theorem profile14_node23 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,17] 6 50 profile14_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,17] 6 50 profile14_node23_cert).mp (by decide +kernel))

def profile14_node24_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 7 22 57 49 49), lower := (rows 19 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 6 22 8 16 32) }] }

theorem profile14_node24 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,18] 6 49 profile14_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,18] 6 49 profile14_node24_cert).mp (by decide +kernel))

def profile14_node25_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 37 58 50 50), lower := (rows 19 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) }] }

theorem profile14_node25 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,33] 6 50 profile14_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,33] 6 50 profile14_node25_cert).mp (by decide +kernel))

def profile14_node26_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 38 57 49 49), lower := (rows 19 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 61 60 8 16 32) }] }

theorem profile14_node26 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,34] 6 49 profile14_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,34] 6 49 profile14_node26_cert).mp (by decide +kernel))

def profile14_node27_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 19 7 52 59 51 51), lower := (rows 19 7 52 8 16 32), losses := [{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 19 7 23 8 16 0) }] }

theorem profile14_node27 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,48] 6 51 profile14_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5,48] 6 51 profile14_node27_cert).mp (by decide +kernel))

def profile14_node21_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node21 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node21_route profile14_node21_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node22
  · exact profile14_node23
  · exact profile14_node24
  · exact profile14_node25
  · exact profile14_node26
  · exact profile14_node27

def profile14_node28_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 19 19 55 63 55 55), lower := (rows 19 19 4 8 16 32), losses := [{ target := 5, region := (rows 19 19 4 8 16 0), good := (rows 19 19 4 8 19 0) }] }

theorem profile14_node28 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,17] 6 55 profile14_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,17] 6 55 profile14_node28_cert).mp (by decide +kernel))

def profile14_node29_cert : CutBound 6 := { lost := (rows 32 0 0 0 0 0), upper := (rows 19 22 55 59 51 51), lower := (rows 19 22 4 8 16 32), losses := [{ target := 5, region := (rows 3 2 4 8 16 0), good := (rows 19 23 4 8 16 0) }] }

theorem profile14_node29 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,20] 6 51 profile14_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,20] 6 51 profile14_node29_cert).mp (by decide +kernel))

def profile14_node31_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 7 60 52 52), lower := (rows 19 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 62 8 16 32) }] }

theorem profile14_node31 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,3] 6 52 profile14_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,3] 6 52 profile14_node31_cert).mp (by decide +kernel))

def profile14_node32_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 21 62 54 54), lower := (rows 19 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) }] }

theorem profile14_node32 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,17] 6 54 profile14_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,17] 6 54 profile14_node32_cert).mp (by decide +kernel))

def profile14_node33_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 22 61 53 53), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile14_node33 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,18] 6 53 profile14_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,18] 6 53 profile14_node33_cert).mp (by decide +kernel))

def profile14_node34_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 37 30 22 54), lower := (rows 19 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) }] }

theorem profile14_node34 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,33] 6 22 profile14_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,33] 6 22 profile14_node34_cert).mp (by decide +kernel))

def profile14_node35_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 38 29 21 53), lower := (rows 19 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 22 38 38 8 16 32) }] }

theorem profile14_node35 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,34] 6 21 profile14_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,34] 6 21 profile14_node35_cert).mp (by decide +kernel))

def profile14_node37_cert : Bound 6 := { allowed := (rows 32 16 3 48 0 0), upper := (rows 19 35 52 11 20 52), lower := (rows 19 35 52 11 16 32), losses := [] }

theorem profile14_node37 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,3] 6 20 profile14_node37_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,3] 6 20 profile14_node37_cert).mp (by decide +kernel))

def profile14_node38_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 52 13 18 50), lower := (rows 19 35 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 54 52 60 16 32) }] }

theorem profile14_node38 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,5] 6 18 profile14_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,5] 6 18 profile14_node38_cert).mp (by decide +kernel))

def profile14_node39_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 52 14 17 49), lower := (rows 19 35 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 53 52 60 16 32) }] }

theorem profile14_node39 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,6] 6 17 profile14_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,6] 6 17 profile14_node39_cert).mp (by decide +kernel))

def profile14_node40_cert : Bound 6 := { allowed := (rows 32 16 3 34 0 0), upper := (rows 19 35 52 25 22 38), lower := (rows 19 35 52 25 16 32), losses := [] }

theorem profile14_node40 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,17] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,17] 6 6 profile14_node40_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,17] 6 6 profile14_node40_cert).mp (by decide +kernel))

def profile14_node41_cert : Bound 6 := { allowed := (rows 32 16 3 33 0 0), upper := (rows 19 35 52 26 21 37), lower := (rows 19 35 52 26 16 32), losses := [] }

theorem profile14_node41 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,18] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,18] 6 5 profile14_node41_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,18] 6 5 profile14_node41_cert).mp (by decide +kernel))

def profile14_node42_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 52 28 19 35), lower := (rows 19 35 52 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 18 34 60 28 16 32) }] }

theorem profile14_node42 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,20] 6 3 profile14_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48,20] 6 3 profile14_node42_cert).mp (by decide +kernel))

def profile14_node36_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile14_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node36 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33,48] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile14_node36_route profile14_node36_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node37
  · exact profile14_node38
  · exact profile14_node39
  · exact profile14_node40
  · exact profile14_node41
  · exact profile14_node42

def profile14_node30_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node30 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node30_route profile14_node30_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node31
  · exact profile14_node32
  · exact profile14_node33
  · exact profile14_node34
  · exact profile14_node35
  · exact profile14_node36

def profile14_node44_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 38 7 57 49 49), lower := (rows 19 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 57 60 61 8 16 32) }] }

theorem profile14_node44 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,3] 6 49 profile14_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,3] 6 49 profile14_node44_cert).mp (by decide +kernel))

def profile14_node45_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 38 21 59 51 51), lower := (rows 19 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 36 21 8 16 32) }] }

theorem profile14_node45 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,17] 6 51 profile14_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,17] 6 51 profile14_node45_cert).mp (by decide +kernel))

def profile14_node46_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 38 22 57 49 49), lower := (rows 19 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile14_node46 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,18] 6 49 profile14_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,18] 6 49 profile14_node46_cert).mp (by decide +kernel))

def profile14_node47_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 37 27 19 51), lower := (rows 19 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 38 8 16 32) }] }

theorem profile14_node47 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,33] 6 19 profile14_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,33] 6 19 profile14_node47_cert).mp (by decide +kernel))

def profile14_node48_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 38 38 25 17 49), lower := (rows 19 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 38 38 8 16 32), good := (rows 22 38 38 8 16 38) }] }

theorem profile14_node48 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,34] 6 17 profile14_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,34] 6 17 profile14_node48_cert).mp (by decide +kernel))

def profile14_node49_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 52 27 19 51), lower := (rows 19 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 54 8 16 32) }] }

theorem profile14_node49 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,48] 6 19 profile14_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36,48] 6 19 profile14_node49_cert).mp (by decide +kernel))

def profile14_node43_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node43_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node43 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,36] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node43_route profile14_node43_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node44
  · exact profile14_node45
  · exact profile14_node46
  · exact profile14_node47
  · exact profile14_node48
  · exact profile14_node49

def profile14_node50_cert : CutBound 6 := { lost := (rows 32 0 0 0 0 0), upper := (rows 19 50 55 63 55 55), lower := (rows 19 50 4 8 16 32), losses := [{ target := 5, region := (rows 3 2 4 8 16 0), good := (rows 19 19 4 8 16 0) }] }

theorem profile14_node50 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,48] 6 55 profile14_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18,48] 6 55 profile14_node50_cert).mp (by decide +kernel))

def profile14_node20_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node20 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile14_node20_route profile14_node20_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node21
  · exact profile14_node28
  · exact profile14_node29
  · exact profile14_node30
  · exact profile14_node43
  · exact profile14_node50

def profile14_node52_cert : CutBound 6 := { lost := (rows 0 32 0 0 0 0), upper := (rows 21 19 55 59 51 51), lower := (rows 21 19 4 8 16 32), losses := [{ target := 5, region := (rows 1 3 4 8 16 0), good := (rows 23 19 4 8 16 0) }] }

theorem profile14_node52 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,17] 6 51 profile14_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,17] 6 51 profile14_node52_cert).mp (by decide +kernel))

def profile14_node54_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 21 35 7 58 50 50), lower := (rows 21 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 60 58 62 8 16 32) }] }

theorem profile14_node54 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,3] 6 50 profile14_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,3] 6 50 profile14_node54_cert).mp (by decide +kernel))

def profile14_node55_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 21 35 21 58 50 50), lower := (rows 21 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 20 8 16 32) }] }

theorem profile14_node55 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,17] 6 50 profile14_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,17] 6 50 profile14_node55_cert).mp (by decide +kernel))

def profile14_node56_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 21 35 22 59 51 51), lower := (rows 21 35 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 21 8 16 32) }] }

theorem profile14_node56 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,18] 6 51 profile14_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,18] 6 51 profile14_node56_cert).mp (by decide +kernel))

def profile14_node57_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 21 35 37 26 18 50), lower := (rows 21 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 36 8 16 32) }] }

theorem profile14_node57 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,33] 6 18 profile14_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,33] 6 18 profile14_node57_cert).mp (by decide +kernel))

def profile14_node58_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 21 35 38 27 19 51), lower := (rows 21 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 38 38 8 16 32) }] }

theorem profile14_node58 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,34] 6 19 profile14_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,34] 6 19 profile14_node58_cert).mp (by decide +kernel))

def profile14_node59_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 21 35 52 27 19 51), lower := (rows 21 35 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 53 8 16 32) }] }

theorem profile14_node59 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,48] 6 19 profile14_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33,48] 6 19 profile14_node59_cert).mp (by decide +kernel))

def profile14_node53_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node53_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node53 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node53_route profile14_node53_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node54
  · exact profile14_node55
  · exact profile14_node56
  · exact profile14_node57
  · exact profile14_node58
  · exact profile14_node59

def profile14_node61_cert : CutBound 6 := { lost := (rows 32 0 32 0 0 0), upper := (rows 21 50 7 59 51 51), lower := (rows 21 50 7 8 16 32), losses := [{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 21 23 7 8 16 0) }] }

theorem profile14_node61 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,3] 6 51 profile14_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,3] 6 51 profile14_node61_cert).mp (by decide +kernel))

def profile14_node62_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 50 21 43 51 35), lower := (rows 21 50 21 8 16 32), losses := [{ target := 1, region := (rows 23 0 23 8 16 32), good := (rows 21 53 21 8 21 32) }] }

theorem profile14_node62 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,17] 6 35 profile14_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,17] 6 35 profile14_node62_cert).mp (by decide +kernel))

def profile14_node63_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 21 50 22 43 51 35), lower := (rows 21 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 54 22 8 16 32) }] }

theorem profile14_node63 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,18] 6 35 profile14_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,18] 6 35 profile14_node63_cert).mp (by decide +kernel))

def profile14_node64_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 50 37 27 19 51), lower := (rows 21 50 37 8 16 32), losses := [{ target := 1, region := (rows 3 0 6 8 16 32), good := (rows 21 53 37 8 16 32) }] }

theorem profile14_node64 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,33] 6 19 profile14_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,33] 6 19 profile14_node64_cert).mp (by decide +kernel))

def profile14_node65_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 21 50 38 27 19 51), lower := (rows 21 50 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 54 38 8 16 32) }] }

theorem profile14_node65 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,34] 6 19 profile14_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,34] 6 19 profile14_node65_cert).mp (by decide +kernel))

def profile14_node66_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 21 50 52 11 19 35), lower := (rows 21 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 22 54 54 8 16 32) }] }

theorem profile14_node66 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,48] 6 3 profile14_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48,48] 6 3 profile14_node66_cert).mp (by decide +kernel))

def profile14_node60_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node60_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node60 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20,48] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node60_route profile14_node60_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node61
  · exact profile14_node62
  · exact profile14_node63
  · exact profile14_node64
  · exact profile14_node65
  · exact profile14_node66

def profile14_node51_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node51_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node51 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [20] 6 (by decide) (choices 2) [17,33,48] profile14_node51_route profile14_node51_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node52
  · exact profile14_node53
  · exact profile14_node60

def profile14_node69_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 7 21 58 50 50), lower := (rows 35 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) }] }

theorem profile14_node69 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,17] 6 50 profile14_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,17] 6 50 profile14_node69_cert).mp (by decide +kernel))

def profile14_node70_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 7 22 57 49 49), lower := (rows 35 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 61 60 8 16 32) }] }

theorem profile14_node70 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,18] 6 49 profile14_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,18] 6 49 profile14_node70_cert).mp (by decide +kernel))

def profile14_node71_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 35 7 52 27 19 51), lower := (rows 35 7 52 8 16 32), losses := [{ target := 4, region := (rows 5 6 4 8 0 32), good := (rows 35 7 39 8 0 32) }] }

theorem profile14_node71 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,48] 6 19 profile14_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5,48] 6 19 profile14_node71_cert).mp (by decide +kernel))

def profile14_node68_column : Nat → Fin 6 := fun mask => match mask with | 3 => 4 | 9 => 3 | 33 => 4 | 10 => 3 | 34 => 4 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node68_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node68 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,5] 6 (by decide) (choices 2) [17,18,48] profile14_node68_route profile14_node68_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node69
  · exact profile14_node70
  · exact profile14_node71

def profile14_node73_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 19 7 60 52 52), lower := (rows 35 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 34 18 62 8 16 32) }] }

theorem profile14_node73 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,3] 6 52 profile14_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,3] 6 52 profile14_node73_cert).mp (by decide +kernel))

def profile14_node74_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 19 21 62 54 54), lower := (rows 35 19 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 37 21 21 8 16 32) }] }

theorem profile14_node74 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,17] 6 54 profile14_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,17] 6 54 profile14_node74_cert).mp (by decide +kernel))

def profile14_node75_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 19 22 61 53 53), lower := (rows 35 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 38 22 22 8 16 32) }] }

theorem profile14_node75 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,18] 6 53 profile14_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,18] 6 53 profile14_node75_cert).mp (by decide +kernel))

def profile14_node76_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 19 37 30 22 54), lower := (rows 35 19 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 37 21 37 8 16 32) }] }

theorem profile14_node76 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,33] 6 22 profile14_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,33] 6 22 profile14_node76_cert).mp (by decide +kernel))

def profile14_node77_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 19 38 29 21 53), lower := (rows 35 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 38 22 38 8 16 32) }] }

theorem profile14_node77 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,34] 6 21 profile14_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,34] 6 21 profile14_node77_cert).mp (by decide +kernel))

def profile14_node79_cert : Bound 6 := { allowed := (rows 16 32 3 48 0 0), upper := (rows 35 19 52 11 20 52), lower := (rows 35 19 52 11 16 32), losses := [] }

theorem profile14_node79 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,3] 6 20 profile14_node79_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,3] 6 20 profile14_node79_cert).mp (by decide +kernel))

def profile14_node80_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 19 52 13 18 50), lower := (rows 35 19 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 54 52 60 16 32) }] }

theorem profile14_node80 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,5] 6 18 profile14_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,5] 6 18 profile14_node80_cert).mp (by decide +kernel))

def profile14_node81_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 19 52 14 17 49), lower := (rows 35 19 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 53 52 60 16 32) }] }

theorem profile14_node81 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,6] 6 17 profile14_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,6] 6 17 profile14_node81_cert).mp (by decide +kernel))

def profile14_node82_cert : Bound 6 := { allowed := (rows 16 32 3 34 0 0), upper := (rows 35 19 52 25 22 38), lower := (rows 35 19 52 25 16 32), losses := [] }

theorem profile14_node82 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,17] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,17] 6 6 profile14_node82_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,17] 6 6 profile14_node82_cert).mp (by decide +kernel))

def profile14_node83_cert : Bound 6 := { allowed := (rows 16 32 3 33 0 0), upper := (rows 35 19 52 26 21 37), lower := (rows 35 19 52 26 16 32), losses := [] }

theorem profile14_node83 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,18] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,18] 6 5 profile14_node83_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,18] 6 5 profile14_node83_cert).mp (by decide +kernel))

def profile14_node84_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 19 52 28 19 35), lower := (rows 35 19 52 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 34 18 60 28 16 32) }] }

theorem profile14_node84 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,20] 6 3 profile14_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48,20] 6 3 profile14_node84_cert).mp (by decide +kernel))

def profile14_node78_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile14_node78_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node78 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17,48] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile14_node78_route profile14_node78_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node79
  · exact profile14_node80
  · exact profile14_node81
  · exact profile14_node82
  · exact profile14_node83
  · exact profile14_node84

def profile14_node72_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node72_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node72 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node72_route profile14_node72_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node73
  · exact profile14_node74
  · exact profile14_node75
  · exact profile14_node76
  · exact profile14_node77
  · exact profile14_node78

def profile14_node86_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 22 7 57 49 49), lower := (rows 35 22 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 57 60 61 8 16 32) }] }

theorem profile14_node86 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,3] 6 49 profile14_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,3] 6 49 profile14_node86_cert).mp (by decide +kernel))

def profile14_node87_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 21 59 51 51), lower := (rows 35 22 21 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 34 22 22 8 16 32) }] }

theorem profile14_node87 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,17] 6 51 profile14_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,17] 6 51 profile14_node87_cert).mp (by decide +kernel))

def profile14_node88_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 35 22 22 57 49 49), lower := (rows 35 22 22 8 16 32), losses := [{ target := 0, region := (rows 0 22 22 8 16 32), good := (rows 38 22 22 8 22 32) }] }

theorem profile14_node88 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,18] 6 49 profile14_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,18] 6 49 profile14_node88_cert).mp (by decide +kernel))

def profile14_node89_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 22 37 27 19 51), lower := (rows 35 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 37 20 37 8 16 32) }] }

theorem profile14_node89 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,33] 6 19 profile14_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,33] 6 19 profile14_node89_cert).mp (by decide +kernel))

def profile14_node90_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 22 38 25 17 49), lower := (rows 35 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 38 22 38 8 16 32) }] }

theorem profile14_node90 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,34] 6 17 profile14_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,34] 6 17 profile14_node90_cert).mp (by decide +kernel))

def profile14_node91_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 52 27 19 51), lower := (rows 35 22 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 34 22 54 8 16 32) }] }

theorem profile14_node91 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,48] 6 19 profile14_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20,48] 6 19 profile14_node91_cert).mp (by decide +kernel))

def profile14_node85_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node85_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node85 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,20] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node85_route profile14_node85_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node86
  · exact profile14_node87
  · exact profile14_node88
  · exact profile14_node89
  · exact profile14_node90
  · exact profile14_node91

def profile14_node92_cert : CutBound 6 := { lost := (rows 16 16 0 0 0 0), upper := (rows 35 35 23 31 23 55), lower := (rows 35 35 4 8 16 32), losses := [{ target := 4, region := (rows 35 35 4 8 0 32), good := (rows 35 35 4 8 0 35) }] }

theorem profile14_node92 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,33] 6 23 profile14_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,33] 6 23 profile14_node92_cert).mp (by decide +kernel))

def profile14_node93_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 35 38 23 27 19 51), lower := (rows 35 38 4 8 16 32), losses := [{ target := 4, region := (rows 3 2 4 8 0 32), good := (rows 35 39 4 8 0 32) }] }

theorem profile14_node93 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,36] 6 19 profile14_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,36] 6 19 profile14_node93_cert).mp (by decide +kernel))

def profile14_node94_cert : CutBound 6 := { lost := (rows 16 0 0 0 0 0), upper := (rows 35 50 23 31 23 55), lower := (rows 35 50 4 8 16 32), losses := [{ target := 4, region := (rows 3 2 4 8 0 32), good := (rows 35 35 4 8 0 32) }] }

theorem profile14_node94 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,48] 6 23 profile14_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34,48] 6 23 profile14_node94_cert).mp (by decide +kernel))

def profile14_node67_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node67_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node67 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [34] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile14_node67_route profile14_node67_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node68
  · exact profile14_node72
  · exact profile14_node85
  · exact profile14_node92
  · exact profile14_node93
  · exact profile14_node94

def profile14_node97_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 37 19 7 58 50 50), lower := (rows 37 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 60 58 62 8 16 32) }] }

theorem profile14_node97 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,3] 6 50 profile14_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,3] 6 50 profile14_node97_cert).mp (by decide +kernel))

def profile14_node98_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 37 19 21 58 50 50), lower := (rows 37 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 36 58 20 8 16 32) }] }

theorem profile14_node98 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,17] 6 50 profile14_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,17] 6 50 profile14_node98_cert).mp (by decide +kernel))

def profile14_node99_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 37 19 22 59 51 51), lower := (rows 37 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 36 22 22 8 16 32) }] }

theorem profile14_node99 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,18] 6 51 profile14_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,18] 6 51 profile14_node99_cert).mp (by decide +kernel))

def profile14_node100_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 37 19 37 26 18 50), lower := (rows 37 19 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 36 58 36 8 16 32) }] }

theorem profile14_node100 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,33] 6 18 profile14_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,33] 6 18 profile14_node100_cert).mp (by decide +kernel))

def profile14_node101_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 37 19 38 27 19 51), lower := (rows 37 19 38 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 37 17 37 8 16 32) }] }

theorem profile14_node101 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,34] 6 19 profile14_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,34] 6 19 profile14_node101_cert).mp (by decide +kernel))

def profile14_node102_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 37 19 52 27 19 51), lower := (rows 37 19 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 37 17 53 8 16 32) }] }

theorem profile14_node102 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,48] 6 19 profile14_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17,48] 6 19 profile14_node102_cert).mp (by decide +kernel))

def profile14_node96_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node96_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node96 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node96_route profile14_node96_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node97
  · exact profile14_node98
  · exact profile14_node99
  · exact profile14_node100
  · exact profile14_node101
  · exact profile14_node102

def profile14_node103_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 37 35 23 27 19 51), lower := (rows 37 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 32), good := (rows 39 35 4 8 0 32) }] }

theorem profile14_node103 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,33] 6 19 profile14_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,33] 6 19 profile14_node103_cert).mp (by decide +kernel))

def profile14_node105_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 37 50 7 27 19 51), lower := (rows 37 50 7 8 16 32), losses := [{ target := 4, region := (rows 3 2 6 8 0 32), good := (rows 37 39 7 8 0 32) }] }

theorem profile14_node105 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,3] 6 19 profile14_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,3] 6 19 profile14_node105_cert).mp (by decide +kernel))

def profile14_node106_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 37 50 21 27 19 51), lower := (rows 37 50 21 8 16 32), losses := [{ target := 1, region := (rows 3 0 6 8 16 32), good := (rows 37 53 21 8 16 32) }] }

theorem profile14_node106 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,17] 6 19 profile14_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,17] 6 19 profile14_node106_cert).mp (by decide +kernel))

def profile14_node107_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 37 50 22 27 19 51), lower := (rows 37 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 36 54 22 8 16 32) }] }

theorem profile14_node107 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,18] 6 19 profile14_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48,18] 6 19 profile14_node107_cert).mp (by decide +kernel))

def profile14_node104_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile14_node104_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node104 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36,48] 6 (by decide) (choices 2) [3,17,18] profile14_node104_route profile14_node104_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node105
  · exact profile14_node106
  · exact profile14_node107

def profile14_node95_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node95_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node95 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [36] 6 (by decide) (choices 2) [17,33,48] profile14_node95_route profile14_node95_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node96
  · exact profile14_node103
  · exact profile14_node104

def profile14_node110_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 7 58 50 50), lower := (rows 49 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 48 62 62 8 16 32) }] }

theorem profile14_node110 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,3] 6 50 profile14_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,3] 6 50 profile14_node110_cert).mp (by decide +kernel))

def profile14_node111_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 21 58 50 50), lower := (rows 49 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 20 8 16 32) }] }

theorem profile14_node111 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,17] 6 50 profile14_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,17] 6 50 profile14_node111_cert).mp (by decide +kernel))

def profile14_node112_cert : CutBound 6 := { lost := (rows 0 32 32 0 0 0), upper := (rows 49 7 22 59 51 51), lower := (rows 49 7 22 8 16 32), losses := [{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 7 22 8 16 0) }] }

theorem profile14_node112 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,18] 6 51 profile14_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,18] 6 51 profile14_node112_cert).mp (by decide +kernel))

def profile14_node113_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 37 26 18 50), lower := (rows 49 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 36 8 16 32) }] }

theorem profile14_node113 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,33] 6 18 profile14_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,33] 6 18 profile14_node113_cert).mp (by decide +kernel))

def profile14_node114_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 49 7 38 27 19 51), lower := (rows 49 7 38 8 16 32), losses := [{ target := 4, region := (rows 1 3 5 8 0 32), good := (rows 39 7 38 8 0 32) }] }

theorem profile14_node114 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,34] 6 19 profile14_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,34] 6 19 profile14_node114_cert).mp (by decide +kernel))

def profile14_node115_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 7 52 27 19 51), lower := (rows 49 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 6 52 8 16 32) }] }

theorem profile14_node115 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,48] 6 19 profile14_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5,48] 6 19 profile14_node115_cert).mp (by decide +kernel))

def profile14_node109_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node109_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node109 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node109_route profile14_node109_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node110
  · exact profile14_node111
  · exact profile14_node112
  · exact profile14_node113
  · exact profile14_node114
  · exact profile14_node115

def profile14_node116_cert : CutBound 6 := { lost := (rows 0 32 0 0 0 0), upper := (rows 49 19 55 63 55 55), lower := (rows 49 19 4 8 16 32), losses := [{ target := 5, region := (rows 1 3 4 8 16 0), good := (rows 19 19 4 8 16 0) }] }

theorem profile14_node116 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,17] 6 55 profile14_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,17] 6 55 profile14_node116_cert).mp (by decide +kernel))

def profile14_node118_cert : CutBound 6 := { lost := (rows 0 32 32 0 0 0), upper := (rows 49 22 7 59 51 51), lower := (rows 49 22 7 8 16 32), losses := [{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 22 7 8 16 0) }] }

theorem profile14_node118 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,3] 6 51 profile14_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,3] 6 51 profile14_node118_cert).mp (by decide +kernel))

def profile14_node119_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 22 21 43 51 35), lower := (rows 49 22 21 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 48 22 22 8 16 32) }] }

theorem profile14_node119 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,17] 6 35 profile14_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,17] 6 35 profile14_node119_cert).mp (by decide +kernel))

def profile14_node120_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 22 43 51 35), lower := (rows 49 22 22 8 16 32), losses := [{ target := 0, region := (rows 0 23 23 8 16 32), good := (rows 54 22 22 8 22 32) }] }

theorem profile14_node120 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,18] 6 35 profile14_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,18] 6 35 profile14_node120_cert).mp (by decide +kernel))

def profile14_node121_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 22 37 27 19 51), lower := (rows 49 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 20 37 8 16 32) }] }

theorem profile14_node121 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,33] 6 19 profile14_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,33] 6 19 profile14_node121_cert).mp (by decide +kernel))

def profile14_node122_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 38 27 19 51), lower := (rows 49 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 8 16 32) }] }

theorem profile14_node122 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,34] 6 19 profile14_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,34] 6 19 profile14_node122_cert).mp (by decide +kernel))

def profile14_node123_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 52 11 19 35), lower := (rows 49 22 52 8 16 32), losses := [{ target := 0, region := (rows 0 7 5 8 16 32), good := (rows 54 22 54 8 16 32) }] }

theorem profile14_node123 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,48] 6 3 profile14_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20,48] 6 3 profile14_node123_cert).mp (by decide +kernel))

def profile14_node117_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile14_node117_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node117 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,20] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile14_node117_route profile14_node117_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node118
  · exact profile14_node119
  · exact profile14_node120
  · exact profile14_node121
  · exact profile14_node122
  · exact profile14_node123

def profile14_node124_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 49 35 23 31 23 55), lower := (rows 49 35 4 8 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 32), good := (rows 35 35 4 8 0 32) }] }

theorem profile14_node124 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,33] 6 23 profile14_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,33] 6 23 profile14_node124_cert).mp (by decide +kernel))

def profile14_node126_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 49 38 7 27 19 51), lower := (rows 49 38 7 8 16 32), losses := [{ target := 4, region := (rows 1 3 5 8 0 32), good := (rows 39 38 7 8 0 32) }] }

theorem profile14_node126 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,3] 6 19 profile14_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,3] 6 19 profile14_node126_cert).mp (by decide +kernel))

def profile14_node127_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 38 21 27 19 51), lower := (rows 49 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 36 21 8 16 32) }] }

theorem profile14_node127 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,17] 6 19 profile14_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,17] 6 19 profile14_node127_cert).mp (by decide +kernel))

def profile14_node128_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 38 22 27 19 51), lower := (rows 49 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 38 22 8 16 32) }] }

theorem profile14_node128 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,18] 6 19 profile14_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36,18] 6 19 profile14_node128_cert).mp (by decide +kernel))

def profile14_node125_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile14_node125_route : Route 6 := (fun mask => (mask,id))

theorem profile14_node125 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,36] 6 (by decide) (choices 2) [3,17,18] profile14_node125_route profile14_node125_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node126
  · exact profile14_node127
  · exact profile14_node128

def profile14_node129_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 50 23 31 23 55), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) }] }

theorem profile14_node129 : Upper (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,48] 6 23 profile14_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,32,19,18]) (R (n:=6) [34,34,33,32,19,18]) [48,48] 6 23 profile14_node129_cert).mp (by decide +kernel))


#print axioms profile14_node129
end Delivery.SmallBudgetTenFinite6
