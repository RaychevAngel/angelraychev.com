import SmallBudgetTenFinite6Common

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile13_node3_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 7 11 7 56 48 48), lower := (rows 7 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) },{ target := 1, region := (rows 1 0 4 63 63 63), good := (rows 61 57 61 56 56 56) }] }

theorem profile13_node3 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,3] 6 48 profile13_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,3] 6 48 profile13_node3_cert).mp (by decide +kernel))

def profile13_node5_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 7 11 21 42 48 48), lower := (rows 7 11 21 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 63 63), good := (rows 62 58 60 58 48 48) },{ target := 1, region := (rows 1 0 7 8 63 63), good := (rows 53 61 53 60 48 48) }] }

theorem profile13_node5 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,34] 6 48 profile13_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,34] 6 48 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : CutBound 6 := { lost := (rows 32 32 32 1 0 0), upper := (rows 7 11 21 56 50 34), lower := (rows 7 11 21 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 15 19 35), good := (rows 62 58 60 56 16 32) },{ target := 5, region := (rows 11 10 12 8 16 0), good := (rows 7 15 21 31 16 0) }] }

theorem profile13_node6 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,48] 6 34 profile13_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17,48] 6 34 profile13_node6_cert).mp (by decide +kernel))

def profile13_node4_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 18 => 5 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node4_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node4 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,17] 6 (by decide) (choices 2) [34,48] profile13_node4_route profile13_node4_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node5
  · exact profile13_node6

def profile13_node7_cert : CutBound 6 := { lost := (rows 16 0 0 2 0 0), upper := (rows 7 11 22 57 49 49), lower := (rows 7 11 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 11 7 8 0 32) }] }

theorem profile13_node7 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,18] 6 49 profile13_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,18] 6 49 profile13_node7_cert).mp (by decide +kernel))

def profile13_node9_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 11 52 11 48 48), lower := (rows 7 11 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 62 52 62 52 52) },{ target := 1, region := (rows 1 0 63 8 63 63), good := (rows 53 61 52 61 52 52) }] }

theorem profile13_node9 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,3] 6 48 profile13_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,3] 6 48 profile13_node9_cert).mp (by decide +kernel))

def profile13_node10_cert : CutBound 6 := { lost := (rows 0 16 1 0 0 0), upper := (rows 7 11 52 25 50 34), lower := (rows 7 11 52 25 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 62 52 60 16 32) },{ target := 4, region := (rows 1 10 4 8 0 43), good := (rows 39 43 36 43 0 32) }] }

theorem profile13_node10 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,17] 6 34 profile13_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,17] 6 34 profile13_node10_cert).mp (by decide +kernel))

def profile13_node11_cert : CutBound 6 := { lost := (rows 32 32 2 32 0 0), upper := (rows 7 11 52 26 49 33), lower := (rows 7 11 52 26 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 61 52 60 16 32) },{ target := 5, region := (rows 5 7 4 12 16 0), good := (rows 15 11 31 26 16 0) }] }

theorem profile13_node11 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,18] 6 33 profile13_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,18] 6 33 profile13_node11_cert).mp (by decide +kernel))

def profile13_node12_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 7 11 52 56 19 35), lower := (rows 7 11 52 56 16 32), losses := [{ target := 0, region := (rows 0 2 12 12 16 32), good := (rows 14 14 60 60 16 32) }] }

theorem profile13_node12 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,48] 6 3 profile13_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48,48] 6 3 profile13_node12_cert).mp (by decide +kernel))

def profile13_node8_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node8_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node8 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9,48] 6 (by decide) (choices 2) [3,17,18,48] profile13_node8_route profile13_node8_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node9
  · exact profile13_node10
  · exact profile13_node11
  · exact profile13_node12

def profile13_node2_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node2_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node2 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,9] 6 (by decide) (choices 2) [3,17,18,48] profile13_node2_route profile13_node2_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node3
  · exact profile13_node4
  · exact profile13_node7
  · exact profile13_node8

def profile13_node14_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 7 19 7 56 56 56), lower := (rows 7 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 62 58 62 56 56 56) },{ target := 1, region := (rows 1 0 4 63 63 63), good := (rows 61 57 61 56 56 56) }] }

theorem profile13_node14 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,3] 6 56 profile13_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,3] 6 56 profile13_node14_cert).mp (by decide +kernel))

def profile13_node16_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 7 19 13 42 48 48), lower := (rows 7 19 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 63 63), good := (rows 62 58 60 58 48 48) },{ target := 4, region := (rows 9 2 12 8 0 32), good := (rows 7 3 13 47 0 32) }] }

theorem profile13_node16 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,34] 6 48 profile13_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,34] 6 48 profile13_node16_cert).mp (by decide +kernel))

def profile13_node17_cert : CutBound 6 := { lost := (rows 32 32 32 1 0 0), upper := (rows 7 19 13 56 50 34), lower := (rows 7 19 13 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 15 19 35), good := (rows 62 58 60 56 16 32) },{ target := 5, region := (rows 13 10 12 8 16 0), good := (rows 7 19 15 31 16 0) }] }

theorem profile13_node17 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,48] 6 34 profile13_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9,48] 6 34 profile13_node17_cert).mp (by decide +kernel))

def profile13_node15_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 18 => 5 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node15_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node15 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,9] 6 (by decide) (choices 2) [34,48] profile13_node15_route profile13_node15_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node16
  · exact profile13_node17

def profile13_node18_cert : CutBound 6 := { lost := (rows 16 0 0 2 0 0), upper := (rows 7 19 14 57 49 49), lower := (rows 7 19 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 3 15 8 0 32) }] }

theorem profile13_node18 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,10] 6 49 profile13_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,10] 6 49 profile13_node18_cert).mp (by decide +kernel))

def profile13_node19_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 7 19 21 42 58 42), lower := (rows 7 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 62 58 60 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 5 21 21 8 16 32) }] }

theorem profile13_node19 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,17] 6 42 profile13_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,17] 6 42 profile13_node19_cert).mp (by decide +kernel))

def profile13_node20_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 7 19 22 41 57 41), lower := (rows 7 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 22 22 8 16 32) },{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) }] }

theorem profile13_node20 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,18] 6 41 profile13_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,18] 6 41 profile13_node20_cert).mp (by decide +kernel))

def profile13_node21_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 7 19 28 43 51 35), lower := (rows 7 19 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 47 43 12 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 7 19 31 8 16 0) }] }

theorem profile13_node21 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,24] 6 35 profile13_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,24] 6 35 profile13_node21_cert).mp (by decide +kernel))

def profile13_node23_cert : Bound 6 := { allowed := (rows 48 32 18 32 0 0), upper := (rows 7 19 37 26 56 40), lower := (rows 7 19 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 31 47), good := (rows 62 58 60 58 16 32) }] }

theorem profile13_node23 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,18] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,18] 6 40 profile13_node23_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,18] 6 40 profile13_node23_cert).mp (by decide +kernel))

def profile13_node24_cert : Bound 6 := { allowed := (rows 48 32 18 16 0 0), upper := (rows 7 19 37 42 24 56), lower := (rows 7 19 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 31 47), good := (rows 62 58 60 58 16 32) }] }

theorem profile13_node24 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,34] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,34] 6 24 profile13_node24_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,34] 6 24 profile13_node24_cert).mp (by decide +kernel))

def profile13_node25_cert : Bound 6 := { allowed := (rows 48 32 18 2 0 0), upper := (rows 7 19 37 56 26 42), lower := (rows 7 19 37 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 15 19 35), good := (rows 62 58 60 56 16 32) }] }

theorem profile13_node25 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,48] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,48] 6 10 profile13_node25_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33,48] 6 10 profile13_node25_cert).mp (by decide +kernel))

def profile13_node22_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node22_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node22 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,33] 6 (by decide) (choices 2) [18,34,48] profile13_node22_route profile13_node22_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node23
  · exact profile13_node24
  · exact profile13_node25

def profile13_node26_cert : CutBound 6 := { lost := (rows 16 0 0 2 0 0), upper := (rows 7 19 38 57 57 57), lower := (rows 7 19 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 61 57 60 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 3 39 8 0 32) }] }

theorem profile13_node26 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,34] 6 57 profile13_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,34] 6 57 profile13_node26_cert).mp (by decide +kernel))

def profile13_node28_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 19 44 11 48 48), lower := (rows 7 19 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 63 63), good := (rows 54 50 60 62 48 48) },{ target := 1, region := (rows 1 0 12 8 63 63), good := (rows 53 49 60 61 48 48) }] }

theorem profile13_node28 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,3] 6 48 profile13_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,3] 6 48 profile13_node28_cert).mp (by decide +kernel))

def profile13_node29_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 7 19 44 25 50 34), lower := (rows 7 19 44 25 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 54 50 44 60 16 32) },{ target := 1, region := (rows 1 0 4 10 16 32), good := (rows 13 25 44 25 16 32) }] }

theorem profile13_node29 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,17] 6 34 profile13_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,17] 6 34 profile13_node29_cert).mp (by decide +kernel))

def profile13_node30_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 7 19 44 26 49 33), lower := (rows 7 19 44 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 14 26 44 26 16 32) },{ target := 1, region := (rows 1 0 12 8 19 35), good := (rows 53 49 44 60 16 32) }] }

theorem profile13_node30 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,18] 6 33 profile13_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,18] 6 33 profile13_node30_cert).mp (by decide +kernel))

def profile13_node31_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 19 44 41 18 50), lower := (rows 7 19 44 41 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 54 50 44 60 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 5 17 44 45 16 32) }] }

theorem profile13_node31 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,33] 6 18 profile13_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,33] 6 18 profile13_node31_cert).mp (by decide +kernel))

def profile13_node32_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 19 44 42 17 49), lower := (rows 7 19 44 42 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 6 18 44 46 16 32) },{ target := 1, region := (rows 1 0 12 8 19 35), good := (rows 53 49 44 60 16 32) }] }

theorem profile13_node32 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,34] 6 17 profile13_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,34] 6 17 profile13_node32_cert).mp (by decide +kernel))

def profile13_node33_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 7 19 44 56 19 35), lower := (rows 7 19 44 56 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 6 18 44 60 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 5 17 44 60 16 32) }] }

theorem profile13_node33 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,48] 6 3 profile13_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40,48] 6 3 profile13_node33_cert).mp (by decide +kernel))

def profile13_node27_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node27_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node27 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,40] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node27_route profile13_node27_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node28
  · exact profile13_node29
  · exact profile13_node30
  · exact profile13_node31
  · exact profile13_node32
  · exact profile13_node33

def profile13_node34_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 7 19 52 43 59 43), lower := (rows 7 19 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 47 43 36 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 7 19 23 8 16 0) }] }

theorem profile13_node34 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,48] 6 43 profile13_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17,48] 6 43 profile13_node34_cert).mp (by decide +kernel))

def profile13_node13_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node13_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node13 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,17] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile13_node13_route profile13_node13_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node14
  · exact profile13_node15
  · exact profile13_node18
  · exact profile13_node19
  · exact profile13_node20
  · exact profile13_node21
  · exact profile13_node22
  · exact profile13_node26
  · exact profile13_node27
  · exact profile13_node34

def profile13_node36_cert : CutBound 6 := { lost := (rows 16 0 16 2 0 0), upper := (rows 7 26 7 57 49 49), lower := (rows 7 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 24 61 8 16 32) },{ target := 4, region := (rows 7 2 7 8 0 32), good := (rows 7 15 7 8 0 32) }] }

theorem profile13_node36 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,3] 6 49 profile13_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,3] 6 49 profile13_node36_cert).mp (by decide +kernel))

def profile13_node37_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 7 26 21 43 51 35), lower := (rows 7 26 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 10 45 8 0 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 7 31 21 8 16 0) }] }

theorem profile13_node37 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,17] 6 35 profile13_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,17] 6 35 profile13_node37_cert).mp (by decide +kernel))

def profile13_node38_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 7 26 22 41 49 33), lower := (rows 7 26 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 30 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 24 20 8 16 32) }] }

theorem profile13_node38 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,18] 6 33 profile13_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,18] 6 33 profile13_node38_cert).mp (by decide +kernel))

def profile13_node40_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 7 26 37 11 48 48), lower := (rows 7 26 37 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 63 63), good := (rows 54 58 52 58 48 48) },{ target := 1, region := (rows 1 0 13 8 63 63), good := (rows 53 60 53 61 48 48) }] }

theorem profile13_node40 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,3] 6 48 profile13_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,3] 6 48 profile13_node40_cert).mp (by decide +kernel))

def profile13_node41_cert : CutBound 6 := { lost := (rows 16 1 16 0 0 0), upper := (rows 7 26 37 25 50 34), lower := (rows 7 26 37 25 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 54 58 52 58 16 32) },{ target := 4, region := (rows 3 2 15 8 0 35), good := (rows 39 47 37 45 0 32) }] }

theorem profile13_node41 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,17] 6 34 profile13_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,17] 6 34 profile13_node41_cert).mp (by decide +kernel))

def profile13_node42_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 7 26 37 26 49 33), lower := (rows 7 26 37 26 16 32), losses := [{ target := 0, region := (rows 0 26 4 26 16 32), good := (rows 14 26 36 26 26 32) }] }

theorem profile13_node42 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,18] 6 33 profile13_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,18] 6 33 profile13_node42_cert).mp (by decide +kernel))

def profile13_node43_cert : CutBound 6 := { lost := (rows 0 1 2 2 0 0), upper := (rows 7 26 37 41 18 50), lower := (rows 7 26 37 41 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 54 58 52 58 16 32) },{ target := 1, region := (rows 1 0 12 12 16 32), good := (rows 13 28 45 45 16 32) }] }

theorem profile13_node43 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,33] 6 18 profile13_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,33] 6 18 profile13_node43_cert).mp (by decide +kernel))

def profile13_node44_cert : CutBound 6 := { lost := (rows 16 0 18 0 0 0), upper := (rows 7 26 37 42 17 49), lower := (rows 7 26 37 42 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 21 37), good := (rows 53 24 53 40 16 32) },{ target := 4, region := (rows 11 2 12 8 0 32), good := (rows 7 15 37 47 0 32) }] }

theorem profile13_node44 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,34] 6 17 profile13_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,34] 6 17 profile13_node44_cert).mp (by decide +kernel))

def profile13_node45_cert : CutBound 6 := { lost := (rows 16 1 16 0 0 0), upper := (rows 7 26 37 56 19 35), lower := (rows 7 26 37 56 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 6 26 36 58 16 32) },{ target := 4, region := (rows 3 2 7 8 0 35), good := (rows 39 47 37 40 0 32) }] }

theorem profile13_node45 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,48] 6 3 profile13_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33,48] 6 3 profile13_node45_cert).mp (by decide +kernel))

def profile13_node39_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node39_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node39 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node39_route profile13_node39_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node40
  · exact profile13_node41
  · exact profile13_node42
  · exact profile13_node43
  · exact profile13_node44
  · exact profile13_node45

def profile13_node46_cert : CutBound 6 := { lost := (rows 16 0 0 2 0 0), upper := (rows 7 26 38 57 49 49), lower := (rows 7 26 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 24 36 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 10 39 8 0 32) }] }

theorem profile13_node46 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,34] 6 49 profile13_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,34] 6 49 profile13_node46_cert).mp (by decide +kernel))

def profile13_node48_cert : CutBound 6 := { lost := (rows 0 0 2 16 0 0), upper := (rows 7 26 52 11 49 33), lower := (rows 7 26 52 11 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 25 41), good := (rows 53 60 52 61 16 32) },{ target := 4, region := (rows 1 2 4 9 0 41), good := (rows 47 42 36 43 0 32) }] }

theorem profile13_node48 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,3] 6 33 profile13_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,3] 6 33 profile13_node48_cert).mp (by decide +kernel))

def profile13_node49_cert : CutBound 6 := { lost := (rows 0 32 0 16 0 0), upper := (rows 7 26 52 41 19 35), lower := (rows 7 26 52 41 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 10 36 41 0 32) },{ target := 5, region := (rows 1 10 4 8 25 0), good := (rows 23 26 20 27 16 0) }] }

theorem profile13_node49 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,33] 6 3 profile13_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,33] 6 3 profile13_node49_cert).mp (by decide +kernel))

def profile13_node50_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 7 26 52 42 17 33), lower := (rows 7 26 52 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 12 16 32), good := (rows 14 26 62 42 16 32) }] }

theorem profile13_node50 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,34] 6 1 profile13_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48,34] 6 1 profile13_node50_cert).mp (by decide +kernel))

def profile13_node47_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node47_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node47 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24,48] 6 (by decide) (choices 2) [3,33,34] profile13_node47_route profile13_node47_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node48
  · exact profile13_node49
  · exact profile13_node50

def profile13_node35_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node35_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node35 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,24] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node35_route profile13_node35_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node36
  · exact profile13_node37
  · exact profile13_node38
  · exact profile13_node39
  · exact profile13_node46
  · exact profile13_node47

def profile13_node52_cert : CutBound 6 := { lost := (rows 16 0 16 2 0 0), upper := (rows 7 50 7 57 57 57), lower := (rows 7 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 61 48 61 8 16 32) },{ target := 4, region := (rows 7 2 7 8 0 32), good := (rows 7 39 7 8 0 32) }] }

theorem profile13_node52 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,3] 6 57 profile13_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,3] 6 57 profile13_node52_cert).mp (by decide +kernel))

def profile13_node54_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 7 50 13 11 48 48), lower := (rows 7 50 13 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 62 58 50 50) },{ target := 1, region := (rows 1 0 12 8 63 63), good := (rows 53 48 61 61 48 48) }] }

theorem profile13_node54 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,3] 6 48 profile13_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,3] 6 48 profile13_node54_cert).mp (by decide +kernel))

def profile13_node55_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 7 50 13 25 50 34), lower := (rows 7 50 13 25 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 62 58 50 50) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 5 48 13 29 16 32) }] }

theorem profile13_node55 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,17] 6 34 profile13_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,17] 6 34 profile13_node55_cert).mp (by decide +kernel))

def profile13_node56_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 7 50 13 26 49 33), lower := (rows 7 50 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 14 58 12 26 16 32) },{ target := 4, region := (rows 9 2 12 8 0 45), good := (rows 39 34 45 47 0 32) }] }

theorem profile13_node56 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,18] 6 33 profile13_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,18] 6 33 profile13_node56_cert).mp (by decide +kernel))

def profile13_node57_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 7 50 13 56 19 35), lower := (rows 7 50 13 56 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 14 58 14 58 16 32) }] }

theorem profile13_node57 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,48] 6 3 profile13_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9,48] 6 3 profile13_node57_cert).mp (by decide +kernel))

def profile13_node53_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node53_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node53 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,9] 6 (by decide) (choices 2) [3,17,18,48] profile13_node53_route profile13_node53_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node54
  · exact profile13_node55
  · exact profile13_node56
  · exact profile13_node57

def profile13_node58_cert : CutBound 6 := { lost := (rows 16 0 0 2 0 0), upper := (rows 7 50 14 57 49 49), lower := (rows 7 50 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 48 12 8 16 32) },{ target := 4, region := (rows 5 2 4 8 0 32), good := (rows 7 34 15 8 0 32) }] }

theorem profile13_node58 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,10] 6 49 profile13_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,10] 6 49 profile13_node58_cert).mp (by decide +kernel))

def profile13_node59_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 7 50 21 43 59 43), lower := (rows 7 50 21 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 45 8 0 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 7 23 21 8 16 0) }] }

theorem profile13_node59 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,17] 6 43 profile13_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,17] 6 43 profile13_node59_cert).mp (by decide +kernel))

def profile13_node60_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 7 50 22 41 57 41), lower := (rows 7 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 6 54 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 61 48 20 8 16 32) }] }

theorem profile13_node60 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,18] 6 41 profile13_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,18] 6 41 profile13_node60_cert).mp (by decide +kernel))

def profile13_node62_cert : CutBound 6 := { lost := (rows 0 0 2 16 0 0), upper := (rows 7 50 28 11 49 33), lower := (rows 7 50 28 11 16 32), losses := [{ target := 1, region := (rows 1 0 12 8 25 41), good := (rows 53 48 60 61 16 32) },{ target := 4, region := (rows 1 2 4 9 0 41), good := (rows 47 34 44 43 0 32) }] }

theorem profile13_node62 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,3] 6 33 profile13_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,3] 6 33 profile13_node62_cert).mp (by decide +kernel))

def profile13_node63_cert : CutBound 6 := { lost := (rows 0 0 32 16 0 0), upper := (rows 7 50 28 41 19 35), lower := (rows 7 50 28 41 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 47 34 12 41 0 32) },{ target := 5, region := (rows 1 2 12 8 17 0), good := (rows 23 18 28 29 16 0) }] }

theorem profile13_node63 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,33] 6 3 profile13_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,33] 6 3 profile13_node63_cert).mp (by decide +kernel))

def profile13_node64_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 7 50 28 42 17 33), lower := (rows 7 50 28 42 16 32), losses := [{ target := 0, region := (rows 0 2 6 10 16 32), good := (rows 14 62 28 46 16 32) }] }

theorem profile13_node64 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,34] 6 1 profile13_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24,34] 6 1 profile13_node64_cert).mp (by decide +kernel))

def profile13_node61_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node61_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node61 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,24] 6 (by decide) (choices 2) [3,33,34] profile13_node61_route profile13_node61_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node62
  · exact profile13_node63
  · exact profile13_node64

def profile13_node65_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 7 50 52 11 27 43), lower := (rows 7 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 6 54 54 8 16 32) }] }

theorem profile13_node65 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,48] 6 11 profile13_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48,48] 6 11 profile13_node65_cert).mp (by decide +kernel))

def profile13_node51_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node51_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node51 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6,48] 6 (by decide) (choices 2) [3,9,10,17,18,24,48] profile13_node51_route profile13_node51_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node52
  · exact profile13_node53
  · exact profile13_node58
  · exact profile13_node59
  · exact profile13_node60
  · exact profile13_node61
  · exact profile13_node65

def profile13_node1_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node1_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node1 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [6] 6 (by decide) (choices 2) [9,17,24,48] profile13_node1_route profile13_node1_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node13
  · exact profile13_node35
  · exact profile13_node51

def profile13_node68_cert : CutBound 6 := { lost := (rows 0 0 16 1 0 0), upper := (rows 13 19 7 58 50 50), lower := (rows 13 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 60 58 62 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 13 7 7 8 0 32) }] }

theorem profile13_node68 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,3] 6 50 profile13_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,3] 6 50 profile13_node68_cert).mp (by decide +kernel))

def profile13_node69_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 13 19 21 42 50 34), lower := (rows 13 19 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 12 58 20 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 13 21 21 8 16 32) }] }

theorem profile13_node69 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,17] 6 34 profile13_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,17] 6 34 profile13_node69_cert).mp (by decide +kernel))

def profile13_node70_cert : CutBound 6 := { lost := (rows 16 0 1 16 0 0), upper := (rows 13 19 22 43 51 35), lower := (rows 13 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 12 22 22 8 16 32) },{ target := 4, region := (rows 5 2 4 14 0 38), good := (rows 45 43 47 8 0 32) }] }

theorem profile13_node70 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,18] 6 35 profile13_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,18] 6 35 profile13_node70_cert).mp (by decide +kernel))

def profile13_node72_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 13 19 37 26 50 34), lower := (rows 13 19 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 60 58 36 58 16 32) },{ target := 4, region := (rows 9 2 15 8 0 42), good := (rows 45 39 37 47 0 32) }] }

theorem profile13_node72 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,18] 6 34 profile13_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,18] 6 34 profile13_node72_cert).mp (by decide +kernel))

def profile13_node73_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 13 19 37 42 18 50), lower := (rows 13 19 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 60 58 36 58 16 32) },{ target := 1, region := (rows 9 0 12 8 16 32), good := (rows 13 17 37 45 16 32) }] }

theorem profile13_node73 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,34] 6 18 profile13_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,34] 6 18 profile13_node73_cert).mp (by decide +kernel))

def profile13_node74_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 13 19 37 56 18 34), lower := (rows 13 19 37 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 12 58 36 56 16 32) },{ target := 1, region := (rows 9 0 12 8 16 32), good := (rows 13 17 37 61 16 32) }] }

theorem profile13_node74 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,48] 6 2 profile13_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33,48] 6 2 profile13_node74_cert).mp (by decide +kernel))

def profile13_node71_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node71_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node71 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,33] 6 (by decide) (choices 2) [18,34,48] profile13_node71_route profile13_node71_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node72
  · exact profile13_node73
  · exact profile13_node74

def profile13_node76_cert : CutBound 6 := { lost := (rows 16 0 1 16 0 0), upper := (rows 13 19 38 11 48 48), lower := (rows 13 19 38 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 63 63), good := (rows 60 54 54 62 48 48) },{ target := 4, region := (rows 5 2 4 14 0 32), good := (rows 13 11 47 11 0 32) }] }

theorem profile13_node76 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,3] 6 48 profile13_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,3] 6 48 profile13_node76_cert).mp (by decide +kernel))

def profile13_node77_cert : CutBound 6 := { lost := (rows 2 0 1 2 0 0), upper := (rows 13 19 38 25 50 34), lower := (rows 13 19 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 60 54 54 24 16 32) },{ target := 1, region := (rows 5 0 4 10 16 32), good := (rows 13 25 45 25 16 32) }] }

theorem profile13_node77 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,17] 6 34 profile13_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,17] 6 34 profile13_node77_cert).mp (by decide +kernel))

def profile13_node78_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 13 19 38 26 49 33), lower := (rows 13 19 38 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 12 26 46 26 16 32) },{ target := 4, region := (rows 9 2 14 8 0 43), good := (rows 45 39 38 47 0 32) }] }

theorem profile13_node78 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,18] 6 33 profile13_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,18] 6 33 profile13_node78_cert).mp (by decide +kernel))

def profile13_node79_cert : CutBound 6 := { lost := (rows 2 0 1 2 0 0), upper := (rows 13 19 38 41 18 50), lower := (rows 13 19 38 41 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 60 54 54 40 16 32) },{ target := 1, region := (rows 5 0 4 12 16 32), good := (rows 13 17 45 41 16 32) }] }

theorem profile13_node79 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,33] 6 18 profile13_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,33] 6 18 profile13_node79_cert).mp (by decide +kernel))

def profile13_node80_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 13 19 38 42 17 49), lower := (rows 13 19 38 42 16 32), losses := [{ target := 0, region := (rows 0 2 12 12 16 32), good := (rows 12 18 46 46 16 32) }] }

theorem profile13_node80 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,34] 6 17 profile13_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,34] 6 17 profile13_node80_cert).mp (by decide +kernel))

def profile13_node81_cert : CutBound 6 := { lost := (rows 0 32 16 0 0 0), upper := (rows 13 19 38 56 19 35), lower := (rows 13 19 38 56 16 32), losses := [{ target := 4, region := (rows 1 2 6 8 0 34), good := (rows 13 39 38 40 0 32) },{ target := 5, region := (rows 1 3 4 8 19 0), good := (rows 31 19 22 24 16 0) }] }

theorem profile13_node81 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,48] 6 3 profile13_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34,48] 6 3 profile13_node81_cert).mp (by decide +kernel))

def profile13_node75_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node75_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node75 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,34] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node75_route profile13_node75_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node76
  · exact profile13_node77
  · exact profile13_node78
  · exact profile13_node79
  · exact profile13_node80
  · exact profile13_node81

def profile13_node83_cert : CutBound 6 := { lost := (rows 0 0 1 16 0 0), upper := (rows 13 19 52 11 50 34), lower := (rows 13 19 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 26 42), good := (rows 60 54 52 62 16 32) },{ target := 4, region := (rows 1 2 4 10 0 42), good := (rows 45 43 36 43 0 32) }] }

theorem profile13_node83 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,3] 6 34 profile13_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,3] 6 34 profile13_node83_cert).mp (by decide +kernel))

def profile13_node84_cert : CutBound 6 := { lost := (rows 2 0 1 2 0 0), upper := (rows 13 19 52 41 18 34), lower := (rows 13 19 52 41 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 18 34), good := (rows 12 54 52 40 16 32) },{ target := 1, region := (rows 5 0 4 12 16 32), good := (rows 13 17 61 41 16 32) }] }

theorem profile13_node84 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,33] 6 2 profile13_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,33] 6 2 profile13_node84_cert).mp (by decide +kernel))

def profile13_node85_cert : CutBound 6 := { lost := (rows 0 32 0 16 0 0), upper := (rows 13 19 52 42 19 35), lower := (rows 13 19 52 42 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 13 43 36 42 0 32) },{ target := 5, region := (rows 1 3 4 8 19 0), good := (rows 31 19 20 26 16 0) }] }

theorem profile13_node85 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,34] 6 3 profile13_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48,34] 6 3 profile13_node85_cert).mp (by decide +kernel))

def profile13_node82_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node82_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node82 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17,48] 6 (by decide) (choices 2) [3,33,34] profile13_node82_route profile13_node82_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node83
  · exact profile13_node84
  · exact profile13_node85

def profile13_node67_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node67_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node67 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,17] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node67_route profile13_node67_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node68
  · exact profile13_node69
  · exact profile13_node70
  · exact profile13_node71
  · exact profile13_node75
  · exact profile13_node82

def profile13_node88_cert : CutBound 6 := { lost := (rows 16 1 16 16 0 0), upper := (rows 13 50 7 11 48 48), lower := (rows 13 50 7 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 62 50 54 58 50 50) },{ target := 4, region := (rows 15 2 14 14 0 32), good := (rows 13 47 15 15 0 32) }] }

theorem profile13_node88 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,3] 6 48 profile13_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,3] 6 48 profile13_node88_cert).mp (by decide +kernel))

def profile13_node89_cert : CutBound 6 := { lost := (rows 32 1 32 32 0 0), upper := (rows 13 50 7 25 50 34), lower := (rows 13 50 7 25 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 62 50 54 58 50 50) },{ target := 5, region := (rows 7 2 6 10 16 0), good := (rows 13 31 15 25 16 0) }] }

theorem profile13_node89 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,17] 6 34 profile13_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,17] 6 34 profile13_node89_cert).mp (by decide +kernel))

def profile13_node90_cert : CutBound 6 := { lost := (rows 16 0 16 1 0 0), upper := (rows 13 50 7 26 49 33), lower := (rows 13 50 7 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 12 58 14 26 16 32) },{ target := 4, region := (rows 9 2 12 8 0 45), good := (rows 45 34 39 47 0 32) }] }

theorem profile13_node90 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,18] 6 33 profile13_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,18] 6 33 profile13_node90_cert).mp (by decide +kernel))

def profile13_node91_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 13 50 7 56 19 35), lower := (rows 13 50 7 56 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 14 58 14 58 16 32) }] }

theorem profile13_node91 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,48] 6 3 profile13_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3,48] 6 3 profile13_node91_cert).mp (by decide +kernel))

def profile13_node87_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node87_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node87 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,3] 6 (by decide) (choices 2) [3,17,18,48] profile13_node87_route profile13_node87_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node88
  · exact profile13_node89
  · exact profile13_node90
  · exact profile13_node91

def profile13_node93_cert : CutBound 6 := { lost := (rows 32 1 32 32 0 0), upper := (rows 13 50 21 11 50 34), lower := (rows 13 50 21 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 62 50 54 58 50 50) },{ target := 5, region := (rows 11 2 6 10 16 0), good := (rows 13 31 21 15 16 0) }] }

theorem profile13_node93 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,3] 6 34 profile13_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,3] 6 34 profile13_node93_cert).mp (by decide +kernel))

def profile13_node94_cert : CutBound 6 := { lost := (rows 2 1 2 2 0 0), upper := (rows 13 50 21 41 18 34), lower := (rows 13 50 21 41 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 62 50 54 58 50 50) },{ target := 1, region := (rows 3 0 6 10 16 32), good := (rows 13 61 21 41 16 32) }] }

theorem profile13_node94 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,33] 6 2 profile13_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,33] 6 2 profile13_node94_cert).mp (by decide +kernel))

def profile13_node95_cert : CutBound 6 := { lost := (rows 0 0 0 17 0 0), upper := (rows 13 50 21 42 19 35), lower := (rows 13 50 21 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 12 58 20 42 16 32) },{ target := 4, region := (rows 1 2 4 10 0 32), good := (rows 13 42 5 42 0 32) }] }

theorem profile13_node95 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,34] 6 3 profile13_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17,34] 6 3 profile13_node95_cert).mp (by decide +kernel))

def profile13_node92_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node92_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node92 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,17] 6 (by decide) (choices 2) [3,33,34] profile13_node92_route profile13_node92_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node93
  · exact profile13_node94
  · exact profile13_node95

def profile13_node96_cert : CutBound 6 := { lost := (rows 16 0 1 16 0 0), upper := (rows 13 50 22 43 51 35), lower := (rows 13 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 12 54 22 8 16 32) },{ target := 4, region := (rows 5 2 4 12 0 36), good := (rows 45 34 47 8 0 32) }] }

theorem profile13_node96 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,18] 6 35 profile13_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,18] 6 35 profile13_node96_cert).mp (by decide +kernel))

def profile13_node97_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 13 50 52 11 19 35), lower := (rows 13 50 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 6 8 16 32), good := (rows 14 54 54 8 16 32) }] }

theorem profile13_node97 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,48] 6 3 profile13_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48,48] 6 3 profile13_node97_cert).mp (by decide +kernel))

def profile13_node86_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node86_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node86 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12,48] 6 (by decide) (choices 2) [3,17,18,48] profile13_node86_route profile13_node86_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node87
  · exact profile13_node92
  · exact profile13_node96
  · exact profile13_node97

def profile13_node66_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node66_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node66 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [12] 6 (by decide) (choices 2) [17,48] profile13_node66_route profile13_node66_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node67
  · exact profile13_node86

def profile13_node100_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 19 7 7 56 56 56), lower := (rows 19 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 63 63 63), good := (rows 58 62 62 56 56 56) },{ target := 1, region := (rows 1 0 4 63 63 63), good := (rows 57 61 61 56 56 56) }] }

theorem profile13_node100 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,3] 6 56 profile13_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,3] 6 56 profile13_node100_cert).mp (by decide +kernel))

def profile13_node101_cert : CutBound 6 := { lost := (rows 0 16 0 1 0 0), upper := (rows 19 7 13 58 50 50), lower := (rows 19 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 7 15 8 0 32) }] }

theorem profile13_node101 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,9] 6 50 profile13_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,9] 6 50 profile13_node101_cert).mp (by decide +kernel))

def profile13_node103_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 19 7 14 41 48 48), lower := (rows 19 7 14 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 63 63), good := (rows 57 61 60 57 48 48) },{ target := 4, region := (rows 1 10 12 8 0 32), good := (rows 3 7 14 47 0 32) }] }

theorem profile13_node103 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,33] 6 48 profile13_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,33] 6 48 profile13_node103_cert).mp (by decide +kernel))

def profile13_node104_cert : CutBound 6 := { lost := (rows 32 32 32 2 0 0), upper := (rows 19 7 14 56 49 33), lower := (rows 19 7 14 56 16 32), losses := [{ target := 1, region := (rows 1 0 4 15 19 35), good := (rows 57 61 60 56 16 32) },{ target := 5, region := (rows 9 14 12 8 16 0), good := (rows 19 7 15 31 16 0) }] }

theorem profile13_node104 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,48] 6 33 profile13_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10,48] 6 33 profile13_node104_cert).mp (by decide +kernel))

def profile13_node102_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node102_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node102 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,10] 6 (by decide) (choices 2) [33,48] profile13_node102_route profile13_node102_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node103
  · exact profile13_node104

def profile13_node105_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 19 7 21 42 58 42), lower := (rows 19 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) },{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 5 21 8 16 32) }] }

theorem profile13_node105 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,17] 6 42 profile13_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,17] 6 42 profile13_node105_cert).mp (by decide +kernel))

def profile13_node106_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 7 22 41 57 41), lower := (rows 19 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 6 22 8 16 32) },{ target := 1, region := (rows 1 0 4 11 19 35), good := (rows 57 61 60 8 16 32) }] }

theorem profile13_node106 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,18] 6 41 profile13_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,18] 6 41 profile13_node106_cert).mp (by decide +kernel))

def profile13_node107_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 19 7 28 43 51 35), lower := (rows 19 7 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 43 47 12 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 19 7 31 8 16 0) }] }

theorem profile13_node107 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,24] 6 35 profile13_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,24] 6 35 profile13_node107_cert).mp (by decide +kernel))

def profile13_node108_cert : CutBound 6 := { lost := (rows 0 16 0 1 0 0), upper := (rows 19 7 37 58 58 58), lower := (rows 19 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 19 35), good := (rows 58 62 60 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 7 39 8 0 32) }] }

theorem profile13_node108 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,33] 6 58 profile13_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,33] 6 58 profile13_node108_cert).mp (by decide +kernel))

def profile13_node110_cert : Bound 6 := { allowed := (rows 32 48 17 32 0 0), upper := (rows 19 7 38 25 56 40), lower := (rows 19 7 38 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 31 47), good := (rows 57 61 60 57 16 32) }] }

theorem profile13_node110 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,17] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,17] 6 40 profile13_node110_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,17] 6 40 profile13_node110_cert).mp (by decide +kernel))

def profile13_node111_cert : Bound 6 := { allowed := (rows 32 48 17 16 0 0), upper := (rows 19 7 38 41 24 56), lower := (rows 19 7 38 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 11 31 47), good := (rows 57 61 60 57 16 32) }] }

theorem profile13_node111 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,33] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,33] 6 24 profile13_node111_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,33] 6 24 profile13_node111_cert).mp (by decide +kernel))

def profile13_node112_cert : Bound 6 := { allowed := (rows 32 48 17 1 0 0), upper := (rows 19 7 38 56 25 41), lower := (rows 19 7 38 56 16 32), losses := [{ target := 1, region := (rows 1 0 4 15 19 35), good := (rows 57 61 60 56 16 32) }] }

theorem profile13_node112 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,48] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,48] 6 9 profile13_node112_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34,48] 6 9 profile13_node112_cert).mp (by decide +kernel))

def profile13_node109_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node109_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node109 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,34] 6 (by decide) (choices 2) [17,33,48] profile13_node109_route profile13_node109_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node110
  · exact profile13_node111
  · exact profile13_node112

def profile13_node114_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 19 7 44 11 48 48), lower := (rows 19 7 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 63 63), good := (rows 50 54 60 62 48 48) },{ target := 1, region := (rows 1 0 12 8 63 63), good := (rows 49 53 60 61 48 48) }] }

theorem profile13_node114 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,3] 6 48 profile13_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,3] 6 48 profile13_node114_cert).mp (by decide +kernel))

def profile13_node115_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 7 44 25 50 34), lower := (rows 19 7 44 25 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 54 44 60 16 32) },{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 13 44 25 16 32) }] }

theorem profile13_node115 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,17] 6 34 profile13_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,17] 6 34 profile13_node115_cert).mp (by decide +kernel))

def profile13_node116_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 19 7 44 26 49 33), lower := (rows 19 7 44 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 26 14 44 26 16 32) },{ target := 1, region := (rows 1 0 12 8 19 35), good := (rows 49 53 44 60 16 32) }] }

theorem profile13_node116 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,18] 6 33 profile13_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,18] 6 33 profile13_node116_cert).mp (by decide +kernel))

def profile13_node117_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 19 7 44 41 18 50), lower := (rows 19 7 44 41 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 54 44 60 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 17 5 44 45 16 32) }] }

theorem profile13_node117 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,33] 6 18 profile13_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,33] 6 18 profile13_node117_cert).mp (by decide +kernel))

def profile13_node118_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 19 7 44 42 17 49), lower := (rows 19 7 44 42 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 18 6 44 46 16 32) },{ target := 1, region := (rows 1 0 12 8 19 35), good := (rows 49 53 44 60 16 32) }] }

theorem profile13_node118 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,34] 6 17 profile13_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,34] 6 17 profile13_node118_cert).mp (by decide +kernel))

def profile13_node119_cert : CutBound 6 := { lost := (rows 0 0 3 0 0 0), upper := (rows 19 7 44 56 19 35), lower := (rows 19 7 44 56 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 18 6 44 60 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 17 5 44 60 16 32) }] }

theorem profile13_node119 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,48] 6 3 profile13_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40,48] 6 3 profile13_node119_cert).mp (by decide +kernel))

def profile13_node113_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node113_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node113 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,40] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node113_route profile13_node113_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node114
  · exact profile13_node115
  · exact profile13_node116
  · exact profile13_node117
  · exact profile13_node118
  · exact profile13_node119

def profile13_node120_cert : CutBound 6 := { lost := (rows 32 32 0 16 0 0), upper := (rows 19 7 52 43 59 43), lower := (rows 19 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 11 0 35), good := (rows 43 47 36 8 0 32) },{ target := 5, region := (rows 5 6 4 8 16 0), good := (rows 19 7 23 8 16 0) }] }

theorem profile13_node120 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,48] 6 43 profile13_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5,48] 6 43 profile13_node120_cert).mp (by decide +kernel))

def profile13_node99_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node99_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node99 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile13_node99_route profile13_node99_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node100
  · exact profile13_node101
  · exact profile13_node102
  · exact profile13_node105
  · exact profile13_node106
  · exact profile13_node107
  · exact profile13_node108
  · exact profile13_node109
  · exact profile13_node113
  · exact profile13_node120

def profile13_node122_cert : CutBound 6 := { lost := (rows 0 0 16 2 0 0), upper := (rows 19 14 7 57 49 49), lower := (rows 19 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 57 60 61 8 16 32) },{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 7 14 7 8 0 32) }] }

theorem profile13_node122 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,3] 6 49 profile13_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,3] 6 49 profile13_node122_cert).mp (by decide +kernel))

def profile13_node123_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 14 21 43 51 35), lower := (rows 19 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 12 21 8 16 32) },{ target := 4, region := (rows 1 6 4 13 0 37), good := (rows 43 46 47 8 0 32) }] }

theorem profile13_node123 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,17] 6 35 profile13_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,17] 6 35 profile13_node123_cert).mp (by decide +kernel))

def profile13_node124_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 14 22 41 49 33), lower := (rows 19 14 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 14 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 57 12 20 8 16 32) }] }

theorem profile13_node124 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,18] 6 33 profile13_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,18] 6 33 profile13_node124_cert).mp (by decide +kernel))

def profile13_node126_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 14 37 11 48 48), lower := (rows 19 14 37 11 16 32), losses := [{ target := 1, region := (rows 1 0 13 8 63 63), good := (rows 53 60 53 61 48 48) },{ target := 4, region := (rows 1 6 4 13 0 32), good := (rows 11 14 47 11 0 32) }] }

theorem profile13_node126 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,3] 6 48 profile13_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,3] 6 48 profile13_node126_cert).mp (by decide +kernel))

def profile13_node127_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 19 14 37 25 50 34), lower := (rows 19 14 37 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 12 45 25 16 32) },{ target := 4, region := (rows 1 10 13 8 0 43), good := (rows 39 46 37 47 0 32) }] }

theorem profile13_node127 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,17] 6 34 profile13_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,17] 6 34 profile13_node127_cert).mp (by decide +kernel))

def profile13_node128_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 37 26 49 33), lower := (rows 19 14 37 26 16 32), losses := [{ target := 0, region := (rows 0 6 4 9 16 32), good := (rows 26 14 46 26 16 32) }] }

theorem profile13_node128 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,18] 6 33 profile13_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,18] 6 33 profile13_node128_cert).mp (by decide +kernel))

def profile13_node129_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 14 37 41 18 50), lower := (rows 19 14 37 41 16 32), losses := [{ target := 1, region := (rows 1 0 12 12 16 32), good := (rows 17 12 45 45 16 32) }] }

theorem profile13_node129 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,33] 6 18 profile13_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,33] 6 18 profile13_node129_cert).mp (by decide +kernel))

def profile13_node130_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 37 42 17 49), lower := (rows 19 14 37 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 12 16 32), good := (rows 18 14 46 42 16 32) }] }

theorem profile13_node130 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,34] 6 17 profile13_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,34] 6 17 profile13_node130_cert).mp (by decide +kernel))

def profile13_node131_cert : CutBound 6 := { lost := (rows 32 0 16 0 0 0), upper := (rows 19 14 37 56 19 35), lower := (rows 19 14 37 56 16 32), losses := [{ target := 4, region := (rows 1 2 5 8 0 33), good := (rows 39 14 37 40 0 32) },{ target := 5, region := (rows 3 2 4 8 19 0), good := (rows 19 31 21 24 16 0) }] }

theorem profile13_node131 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,48] 6 3 profile13_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33,48] 6 3 profile13_node131_cert).mp (by decide +kernel))


#print axioms profile13_node131
end Delivery.SmallBudgetTenFinite6
