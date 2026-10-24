import SmallBudgetTenFinite5Common

namespace Delivery.SmallBudgetTenFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile1_node2 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 6 27 profile1_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 6 27 profile1_node2_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 7 11 7 29 29), lower := (rows 7 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile1_node4 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 6 29 profile1_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 6 29 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 7 11 13 31 23), lower := (rows 7 11 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 13 13 8 16) }] }

theorem profile1_node5 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] 6 23 profile1_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] 6 23 profile1_node5_cert).mp (by decide +kernel))

def profile1_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 11 14 29 21), lower := (rows 7 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 14 14 8 16) }] }

theorem profile1_node6 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 6 21 profile1_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 6 21 profile1_node6_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 5 := { lost := (rows 0 0 2 0 2), upper := (rows 7 11 21 11 28), lower := (rows 7 11 21 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 26), good := (rows 21 29 21 29 16) }] }

theorem profile1_node8 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 6 12 profile1_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 6 12 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 7 11 21 13 26), lower := (rows 7 11 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 26 20 12 16) }] }

theorem profile1_node9 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 6 10 profile1_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 6 10 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 11 21 14 25), lower := (rows 7 11 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 10 28 14 16) }] }

theorem profile1_node10 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 6 9 profile1_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 6 9 profile1_node10_cert).mp (by decide +kernel))

def profile1_node7_column : Nat → Fin 5 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | _ => 0

def profile1_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node7 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17] 6 (by decide) (choices 2) [3,5,6] profile1_node7_route profile1_node7_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node8
  · exact profile1_node9
  · exact profile1_node10

def profile1_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 7 11 22 13 29), lower := (rows 7 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile1_node11 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] 6 13 profile1_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] 6 13 profile1_node11_cert).mp (by decide +kernel))

def profile1_node12_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 7 11 28 15 23), lower := (rows 7 11 28 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 20 0 16) }] }

theorem profile1_node12 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] 6 7 profile1_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] 6 7 profile1_node12_cert).mp (by decide +kernel))

def profile1_node3_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile1_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node3_route profile1_node3_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node4
  · exact profile1_node5
  · exact profile1_node6
  · exact profile1_node7
  · exact profile1_node11
  · exact profile1_node12

def profile1_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 14 31 27 27), lower := (rows 7 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile1_node13 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] 6 27 profile1_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] 6 27 profile1_node13_cert).mp (by decide +kernel))

def profile1_node16_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 7 19 13 11 28), lower := (rows 7 19 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 18 28 10 16) }] }

theorem profile1_node16 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 6 12 profile1_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 6 12 profile1_node16_cert).mp (by decide +kernel))

def profile1_node17_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 7 19 13 13 26), lower := (rows 7 19 13 13 16), losses := [{ target := 1, region := (rows 1 0 15 15 16), good := (rows 13 29 13 13 16) }] }

theorem profile1_node17 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 6 10 profile1_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 6 10 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 19 13 14 25), lower := (rows 7 19 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 12 14 16) }] }

theorem profile1_node18 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 6 9 profile1_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 6 9 profile1_node18_cert).mp (by decide +kernel))

def profile1_node15_column : Nat → Fin 5 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | _ => 0

def profile1_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node15 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9] 6 (by decide) (choices 2) [3,5,6] profile1_node15_route profile1_node15_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node16
  · exact profile1_node17
  · exact profile1_node18

def profile1_node19_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 7 19 14 13 29), lower := (rows 7 19 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) }] }

theorem profile1_node19 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] 6 13 profile1_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] 6 13 profile1_node19_cert).mp (by decide +kernel))

def profile1_node14_column : Nat → Fin 5 := fun mask => match mask with | 3 => 3 | 17 => 3 | 18 => 3 | 24 => 4 | _ => 0

def profile1_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node14 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17] 6 (by decide) (choices 2) [9,10] profile1_node14_route profile1_node14_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node15
  · exact profile1_node19

def profile1_node20_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 22 15 11 27), lower := (rows 7 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile1_node20 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] 6 11 profile1_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] 6 11 profile1_node20_cert).mp (by decide +kernel))

def profile1_node22_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 7 26 7 13 29), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) }] }

theorem profile1_node22 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 6 13 profile1_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 6 13 profile1_node22_cert).mp (by decide +kernel))

def profile1_node23_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 7 26 13 15 23), lower := (rows 7 26 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 21 0 16) }] }

theorem profile1_node23 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] 6 7 profile1_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] 6 7 profile1_node23_cert).mp (by decide +kernel))

def profile1_node21_column : Nat → Fin 5 := fun mask => match mask with | 17 => 4 | 10 => 0 | 18 => 0 | 24 => 0 | _ => 0

def profile1_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node21 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24] 6 (by decide) (choices 2) [3,9] profile1_node21_route profile1_node21_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node22
  · exact profile1_node23

def profile1_node1_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6] 6 (by decide) (choices 2) [5,9,12,17,20,24] profile1_node1_route profile1_node1_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node13
  · exact profile1_node14
  · exact profile1_node20
  · exact profile1_node21

def profile1_node26_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 19 7 13 15 31), lower := (rows 19 7 13 8 16), losses := [{ target := 3, region := (rows 1 6 4 0 16), good := (rows 19 7 7 0 16) }] }

theorem profile1_node26 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] 6 15 profile1_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] 6 15 profile1_node26_cert).mp (by decide +kernel))

def profile1_node27_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 19 7 14 13 29), lower := (rows 19 7 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) }] }

theorem profile1_node27 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] 6 13 profile1_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] 6 13 profile1_node27_cert).mp (by decide +kernel))

def profile1_node25_column : Nat → Fin 5 := fun mask => match mask with | 3 => 3 | 17 => 3 | 18 => 3 | 24 => 4 | _ => 0

def profile1_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node25 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5] 6 (by decide) (choices 2) [9,10] profile1_node25_route profile1_node25_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node26
  · exact profile1_node27

def profile1_node29_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 19 14 7 13 29), lower := (rows 19 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 17 28 29 8 16) }] }

theorem profile1_node29 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] 6 13 profile1_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] 6 13 profile1_node29_cert).mp (by decide +kernel))

def profile1_node30_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 19 14 13 15 23), lower := (rows 19 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 18 14 14 8 16) }] }

theorem profile1_node30 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] 6 7 profile1_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] 6 7 profile1_node30_cert).mp (by decide +kernel))

def profile1_node28_column : Nat → Fin 5 := fun mask => match mask with | 17 => 4 | 10 => 0 | 18 => 0 | 24 => 0 | _ => 0

def profile1_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node28 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12] 6 (by decide) (choices 2) [3,9] profile1_node28_route profile1_node28_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node29
  · exact profile1_node30

def profile1_node24_column : Nat → Fin 5 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | _ => 0

def profile1_node24_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile1_node24 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18] 6 (by decide) (choices 2) [5,12] profile1_node24_route profile1_node24_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node25
  · exact profile1_node28

def profile1_node0_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile1_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 6 (by decide) (choices 2) [6,18] profile1_node0_route profile1_node0_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node1
  · exact profile1_node24

theorem profile1 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite5
