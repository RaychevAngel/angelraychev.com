import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile11_node3_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 7 57 49 49), lower := (rows 7 19 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 15 23 39), good := (rows 61 57 61 8 16 32) }] }

theorem profile11_node3 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,3] 6 49 profile11_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,3] 6 49 profile11_node3_cert).mp (by decide +kernel))

def profile11_node4_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 7 19 21 43 51 35), lower := (rows 7 19 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 5 21 21 8 16 32) }] }

theorem profile11_node4 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,17] 6 35 profile11_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,17] 6 35 profile11_node4_cert).mp (by decide +kernel))

def profile11_node5_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 19 22 41 49 33), lower := (rows 7 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 22 22 8 16 32) }] }

theorem profile11_node5 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,18] 6 33 profile11_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,18] 6 33 profile11_node5_cert).mp (by decide +kernel))

def profile11_node7_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 7 19 37 11 48 48), lower := (rows 7 19 37 11 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 63 63), good := (rows 53 53 53 61 48 48) }] }

theorem profile11_node7 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,3] 6 48 profile11_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,3] 6 48 profile11_node7_cert).mp (by decide +kernel))

def profile11_node8_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 37 25 50 34), lower := (rows 7 19 37 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 16 32), good := (rows 13 25 37 25 16 32) }] }

theorem profile11_node8 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,17] 6 34 profile11_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,17] 6 34 profile11_node8_cert).mp (by decide +kernel))

def profile11_node9_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 7 19 37 26 49 33), lower := (rows 7 19 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 14 26 36 26 16 32) }] }

theorem profile11_node9 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,18] 6 33 profile11_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,18] 6 33 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 7 19 37 41 18 50), lower := (rows 7 19 37 41 16 32), losses := [{ target := 1, region := (rows 1 0 12 12 16 32), good := (rows 13 17 45 45 16 32) }] }

theorem profile11_node10 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,33] 6 18 profile11_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,33] 6 18 profile11_node10_cert).mp (by decide +kernel))

def profile11_node11_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 7 19 37 42 17 49), lower := (rows 7 19 37 42 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 23 39), good := (rows 53 53 53 60 16 32) }] }

theorem profile11_node11 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,34] 6 17 profile11_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,34] 6 17 profile11_node11_cert).mp (by decide +kernel))

def profile11_node12_cert : CutBound 6 := { lost := (rows 16 0 16 0 0 0), upper := (rows 7 19 37 56 19 35), lower := (rows 7 19 37 56 16 32), losses := [{ target := 4, region := (rows 3 2 7 8 0 35), good := (rows 39 39 37 40 0 32) }] }

theorem profile11_node12 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,48] 6 3 profile11_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33,48] 6 3 profile11_node12_cert).mp (by decide +kernel))

def profile11_node6_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile11_node6_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node6 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node6_route profile11_node6_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node7
  · exact profile11_node8
  · exact profile11_node9
  · exact profile11_node10
  · exact profile11_node11
  · exact profile11_node12

def profile11_node13_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 19 38 57 49 49), lower := (rows 7 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) }] }

theorem profile11_node13 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,34] 6 49 profile11_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,34] 6 49 profile11_node13_cert).mp (by decide +kernel))

def profile11_node14_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 19 52 43 51 35), lower := (rows 7 19 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 47 43 36 8 0 32) }] }

theorem profile11_node14 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,48] 6 35 profile11_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17,48] 6 35 profile11_node14_cert).mp (by decide +kernel))

def profile11_node2_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node2_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node2 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node2_route profile11_node2_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node3
  · exact profile11_node4
  · exact profile11_node5
  · exact profile11_node6
  · exact profile11_node13
  · exact profile11_node14

def profile11_node16_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 7 50 7 57 49 49), lower := (rows 7 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 48 61 8 16 32) }] }

theorem profile11_node16 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,3] 6 49 profile11_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,3] 6 49 profile11_node16_cert).mp (by decide +kernel))

def profile11_node17_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 7 50 21 43 51 35), lower := (rows 7 50 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 45 8 0 32) }] }

theorem profile11_node17 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,17] 6 35 profile11_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,17] 6 35 profile11_node17_cert).mp (by decide +kernel))

def profile11_node18_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 7 50 22 41 49 33), lower := (rows 7 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 22 8 16 32) }] }

theorem profile11_node18 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,18] 6 33 profile11_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,18] 6 33 profile11_node18_cert).mp (by decide +kernel))

def profile11_node19_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 7 50 52 11 19 35), lower := (rows 7 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 6 54 54 8 16 32) }] }

theorem profile11_node19 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,48] 6 3 profile11_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48,48] 6 3 profile11_node19_cert).mp (by decide +kernel))

def profile11_node15_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node15_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile11_node15 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6,48] 6 (by decide) (choices 2) [3,17,18,48] profile11_node15_route profile11_node15_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node16
  · exact profile11_node17
  · exact profile11_node18
  · exact profile11_node19

def profile11_node1_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node1_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile11_node1 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [6] 6 (by decide) (choices 2) [17,48] profile11_node1_route profile11_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node2
  · exact profile11_node15

def profile11_node22_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 7 57 49 49), lower := (rows 19 7 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 15 23 39), good := (rows 57 61 61 8 16 32) }] }

theorem profile11_node22 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,3] 6 49 profile11_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,3] 6 49 profile11_node22_cert).mp (by decide +kernel))

def profile11_node23_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 7 21 43 51 35), lower := (rows 19 7 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 5 21 8 16 32) }] }

theorem profile11_node23 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,17] 6 35 profile11_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,17] 6 35 profile11_node23_cert).mp (by decide +kernel))

def profile11_node24_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 7 22 41 49 33), lower := (rows 19 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 6 22 8 16 32) }] }

theorem profile11_node24 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,18] 6 33 profile11_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,18] 6 33 profile11_node24_cert).mp (by decide +kernel))

def profile11_node25_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 19 7 37 59 51 51), lower := (rows 19 7 37 8 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 7 39 8 0 32) }] }

theorem profile11_node25 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,33] 6 51 profile11_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,33] 6 51 profile11_node25_cert).mp (by decide +kernel))

def profile11_node26_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 38 57 49 49), lower := (rows 19 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 61 60 8 16 32) }] }

theorem profile11_node26 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,34] 6 49 profile11_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,34] 6 49 profile11_node26_cert).mp (by decide +kernel))

def profile11_node27_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 19 7 52 43 51 35), lower := (rows 19 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 43 47 36 8 0 32) }] }

theorem profile11_node27 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,48] 6 35 profile11_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5,48] 6 35 profile11_node27_cert).mp (by decide +kernel))

def profile11_node21_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node21_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node21 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node21_route profile11_node21_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node22
  · exact profile11_node23
  · exact profile11_node24
  · exact profile11_node25
  · exact profile11_node26
  · exact profile11_node27

def profile11_node28_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 19 39 47 55 39), lower := (rows 19 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 35), good := (rows 47 47 4 8 0 32) }] }

theorem profile11_node28 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,17] 6 39 profile11_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,17] 6 39 profile11_node28_cert).mp (by decide +kernel))

def profile11_node29_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 22 39 43 51 35), lower := (rows 19 22 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 6 4 8 0 32) }] }

theorem profile11_node29 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,20] 6 35 profile11_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,20] 6 35 profile11_node29_cert).mp (by decide +kernel))

def profile11_node31_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 35 7 61 53 53), lower := (rows 19 35 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 33 61 8 16 32) }] }

theorem profile11_node31 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,3] 6 53 profile11_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,3] 6 53 profile11_node31_cert).mp (by decide +kernel))

def profile11_node32_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 21 47 55 39), lower := (rows 19 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) }] }

theorem profile11_node32 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,17] 6 39 profile11_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,17] 6 39 profile11_node32_cert).mp (by decide +kernel))

def profile11_node33_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 22 45 53 37), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile11_node33 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,18] 6 37 profile11_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,18] 6 37 profile11_node33_cert).mp (by decide +kernel))

def profile11_node34_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 37 31 23 55), lower := (rows 19 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) }] }

theorem profile11_node34 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,33] 6 23 profile11_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,33] 6 23 profile11_node34_cert).mp (by decide +kernel))

def profile11_node35_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 38 29 21 53), lower := (rows 19 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 22 38 38 8 16 32) }] }

theorem profile11_node35 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,34] 6 21 profile11_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,34] 6 21 profile11_node35_cert).mp (by decide +kernel))

def profile11_node37_cert : Bound 6 := { allowed := (rows 32 16 3 48 0 0), upper := (rows 19 35 52 11 21 37), lower := (rows 19 35 52 11 16 32), losses := [] }

theorem profile11_node37 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,3] 6 5 profile11_node37_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,3] 6 5 profile11_node37_cert).mp (by decide +kernel))

def profile11_node38_cert : CutBound 6 := { lost := (rows 0 16 0 0 0 0), upper := (rows 19 35 52 13 19 35), lower := (rows 19 35 52 13 16 32), losses := [{ target := 4, region := (rows 1 11 4 8 0 43), good := (rows 35 35 36 47 0 32) }] }

theorem profile11_node38 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,5] 6 3 profile11_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,5] 6 3 profile11_node38_cert).mp (by decide +kernel))

def profile11_node39_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 52 14 17 33), lower := (rows 19 35 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 53 52 60 16 32) }] }

theorem profile11_node39 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,6] 6 1 profile11_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48,6] 6 1 profile11_node39_cert).mp (by decide +kernel))

def profile11_node36_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile11_node36_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node36 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33,48] 6 (by decide) (choices 2) [3,5,6] profile11_node36_route profile11_node36_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node37
  · exact profile11_node38
  · exact profile11_node39

def profile11_node30_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node30_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node30 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node30_route profile11_node30_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node31
  · exact profile11_node32
  · exact profile11_node33
  · exact profile11_node34
  · exact profile11_node35
  · exact profile11_node36

def profile11_node41_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 38 7 57 49 49), lower := (rows 19 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 57 60 61 8 16 32) }] }

theorem profile11_node41 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,3] 6 49 profile11_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,3] 6 49 profile11_node41_cert).mp (by decide +kernel))

def profile11_node42_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 38 21 43 51 35), lower := (rows 19 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 36 21 8 16 32) }] }

theorem profile11_node42 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,17] 6 35 profile11_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,17] 6 35 profile11_node42_cert).mp (by decide +kernel))

def profile11_node43_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 38 22 41 49 33), lower := (rows 19 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile11_node43 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,18] 6 33 profile11_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,18] 6 33 profile11_node43_cert).mp (by decide +kernel))

def profile11_node44_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 37 27 19 51), lower := (rows 19 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 38 8 16 32) }] }

theorem profile11_node44 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,33] 6 19 profile11_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,33] 6 19 profile11_node44_cert).mp (by decide +kernel))

def profile11_node45_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 38 38 25 17 49), lower := (rows 19 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 38 38 8 16 32), good := (rows 22 38 38 8 16 38) }] }

theorem profile11_node45 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,34] 6 17 profile11_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,34] 6 17 profile11_node45_cert).mp (by decide +kernel))

def profile11_node46_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 52 11 19 35), lower := (rows 19 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 54 8 16 32) }] }

theorem profile11_node46 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,48] 6 3 profile11_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36,48] 6 3 profile11_node46_cert).mp (by decide +kernel))

def profile11_node40_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node40_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node40 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,36] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node40_route profile11_node40_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node41
  · exact profile11_node42
  · exact profile11_node43
  · exact profile11_node44
  · exact profile11_node45
  · exact profile11_node46

def profile11_node47_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 50 39 47 55 39), lower := (rows 19 50 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 34 4 8 0 32) }] }

theorem profile11_node47 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,48] 6 39 profile11_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18,48] 6 39 profile11_node47_cert).mp (by decide +kernel))

def profile11_node20_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node20_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node20 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile11_node20_route profile11_node20_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node21
  · exact profile11_node28
  · exact profile11_node29
  · exact profile11_node30
  · exact profile11_node40
  · exact profile11_node47

def profile11_node49_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 21 19 39 43 51 35), lower := (rows 21 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 5 47 4 8 0 32) }] }

theorem profile11_node49 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,17] 6 35 profile11_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,17] 6 35 profile11_node49_cert).mp (by decide +kernel))

def profile11_node51_cert : CutBound 6 := { lost := (rows 0 0 16 0 0 0), upper := (rows 21 35 7 59 51 51), lower := (rows 21 35 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 39 7 8 0 32) }] }

theorem profile11_node51 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,3] 6 51 profile11_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,3] 6 51 profile11_node51_cert).mp (by decide +kernel))

def profile11_node52_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 35 21 43 51 35), lower := (rows 21 35 21 8 16 32), losses := [{ target := 1, region := (rows 21 0 21 8 16 32), good := (rows 21 37 21 8 21 32) }] }

theorem profile11_node52 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,17] 6 35 profile11_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,17] 6 35 profile11_node52_cert).mp (by decide +kernel))

def profile11_node53_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 21 35 22 43 51 35), lower := (rows 21 35 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 21 8 16 32) }] }

theorem profile11_node53 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,18] 6 35 profile11_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,18] 6 35 profile11_node53_cert).mp (by decide +kernel))

def profile11_node54_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 21 35 37 27 19 51), lower := (rows 21 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) }] }

theorem profile11_node54 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,33] 6 19 profile11_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,33] 6 19 profile11_node54_cert).mp (by decide +kernel))

def profile11_node55_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 21 35 38 27 19 51), lower := (rows 21 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 38 38 8 16 32) }] }

theorem profile11_node55 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,34] 6 19 profile11_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,34] 6 19 profile11_node55_cert).mp (by decide +kernel))

def profile11_node56_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 21 35 52 11 19 35), lower := (rows 21 35 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 53 8 16 32) }] }

theorem profile11_node56 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,48] 6 3 profile11_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33,48] 6 3 profile11_node56_cert).mp (by decide +kernel))

def profile11_node50_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node50_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node50 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile11_node50_route profile11_node50_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node51
  · exact profile11_node52
  · exact profile11_node53
  · exact profile11_node54
  · exact profile11_node55
  · exact profile11_node56

def profile11_node58_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 21 50 7 43 51 35), lower := (rows 21 50 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 45 34 47 8 0 32) }] }

theorem profile11_node58 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,3] 6 35 profile11_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,3] 6 35 profile11_node58_cert).mp (by decide +kernel))

def profile11_node59_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 50 37 11 19 35), lower := (rows 21 50 37 8 16 32), losses := [{ target := 1, region := (rows 3 0 6 8 16 32), good := (rows 21 53 37 8 16 32) }] }

theorem profile11_node59 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,33] 6 3 profile11_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,33] 6 3 profile11_node59_cert).mp (by decide +kernel))

def profile11_node60_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 21 50 38 11 19 35), lower := (rows 21 50 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 54 38 8 16 32) }] }

theorem profile11_node60 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,34] 6 3 profile11_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48,34] 6 3 profile11_node60_cert).mp (by decide +kernel))

def profile11_node57_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile11_node57_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node57 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20,48] 6 (by decide) (choices 2) [3,33,34] profile11_node57_route profile11_node57_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node58
  · exact profile11_node59
  · exact profile11_node60

def profile11_node48_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node48_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node48 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [20] 6 (by decide) (choices 2) [17,33,48] profile11_node48_route profile11_node48_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node49
  · exact profile11_node50
  · exact profile11_node57

def profile11_node63_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 49 7 7 59 51 51), lower := (rows 49 7 7 8 16 32), losses := [{ target := 4, region := (rows 1 7 7 8 0 32), good := (rows 39 7 7 8 0 32) }] }

theorem profile11_node63 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,3] 6 51 profile11_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,3] 6 51 profile11_node63_cert).mp (by decide +kernel))

def profile11_node64_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 7 21 43 51 35), lower := (rows 49 7 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 5 21 8 16 32) }] }

theorem profile11_node64 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,17] 6 35 profile11_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,17] 6 35 profile11_node64_cert).mp (by decide +kernel))

def profile11_node65_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 7 22 43 51 35), lower := (rows 49 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 46 8 0 32) }] }

theorem profile11_node65 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,18] 6 35 profile11_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,18] 6 35 profile11_node65_cert).mp (by decide +kernel))

def profile11_node66_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 7 52 11 19 35), lower := (rows 49 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 6 52 8 16 32) }] }

theorem profile11_node66 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,48] 6 3 profile11_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5,48] 6 3 profile11_node66_cert).mp (by decide +kernel))

def profile11_node62_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node62_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile11_node62 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,5] 6 (by decide) (choices 2) [3,17,18,48] profile11_node62_route profile11_node62_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node63
  · exact profile11_node64
  · exact profile11_node65
  · exact profile11_node66

def profile11_node67_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 49 19 39 47 55 39), lower := (rows 49 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 33 47 4 8 0 32) }] }

theorem profile11_node67 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,17] 6 39 profile11_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,17] 6 39 profile11_node67_cert).mp (by decide +kernel))

def profile11_node69_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 22 7 43 51 35), lower := (rows 49 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 33 46 47 8 0 32) }] }

theorem profile11_node69 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,3] 6 35 profile11_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,3] 6 35 profile11_node69_cert).mp (by decide +kernel))

def profile11_node70_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 22 37 11 19 35), lower := (rows 49 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 20 37 8 16 32) }] }

theorem profile11_node70 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,33] 6 3 profile11_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,33] 6 3 profile11_node70_cert).mp (by decide +kernel))

def profile11_node71_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 38 11 19 35), lower := (rows 49 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 8 16 32) }] }

theorem profile11_node71 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,34] 6 3 profile11_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20,34] 6 3 profile11_node71_cert).mp (by decide +kernel))

def profile11_node68_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile11_node68_route : Route 6 := (fun mask => (mask,id))

theorem profile11_node68 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,20] 6 (by decide) (choices 2) [3,33,34] profile11_node68_route profile11_node68_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node69
  · exact profile11_node70
  · exact profile11_node71

def profile11_node72_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 50 7 15 23 39), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) }] }

theorem profile11_node72 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,48] 6 7 profile11_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48,48] 6 7 profile11_node72_cert).mp (by decide +kernel))

def profile11_node61_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node61_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile11_node61 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [48] 6 (by decide) (choices 2) [5,17,20,48] profile11_node61_route profile11_node61_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node62
  · exact profile11_node67
  · exact profile11_node68
  · exact profile11_node72

def profile11_node0_column : Nat → Fin 6 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile11_node0_route : Route 6 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile11_node0 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [] 6 (by decide) (choices 2) [6,18,20,48] profile11_node0_route profile11_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node1
  · exact profile11_node20
  · exact profile11_node48
  · exact profile11_node61

theorem profile11 : Upper (D (n:=6) [35,34,33,32,18,18]) (R (n:=6) [35,34,33,32,18,18]) [] 6 := profile11_node0


#print axioms profile11
end Delivery.SmallBudgetTenFinite6
