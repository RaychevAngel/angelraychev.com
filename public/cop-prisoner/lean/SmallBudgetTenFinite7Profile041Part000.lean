import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile41_node3_cert : Bound 7 := { allowed := (rows 56 48 32 0 0 0 0), upper := (rows 7 11 28 120 112 112 112), lower := (rows 7 11 28 8 16 32 64), losses := [] }

theorem profile41_node3 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,24] 6 112 profile41_node3_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,24] 6 112 profile41_node3_cert).mp (by decide +kernel))

def profile41_node4_cert : Bound 7 := { allowed := (rows 56 48 8 0 0 0 0), upper := (rows 7 11 52 120 120 120 120), lower := (rows 7 11 52 8 16 32 64), losses := [] }

theorem profile41_node4 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,48] 6 120 profile41_node4_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,48] 6 120 profile41_node4_cert).mp (by decide +kernel))

def profile41_node5_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 11 76 56 48 48 112), lower := (rows 7 11 76 8 16 32 64), losses := [{ target := 4, region := (rows 5 6 4 8 0 32 64), good := (rows 7 11 79 8 0 32 64) }] }

theorem profile41_node5 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,72] 6 48 profile41_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,72] 6 48 profile41_node5_cert).mp (by decide +kernel))

def profile41_node7_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 7 11 84 24 56 40 104), lower := (rows 7 11 84 24 16 32 64), losses := [{ target := 5, region := (rows 5 7 4 28 16 0 64), good := (rows 15 11 95 24 24 0 64) }] }

theorem profile41_node7 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,16] 6 40 profile41_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,16] 6 40 profile41_node7_cert).mp (by decide +kernel))

def profile41_node9_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 7 11 84 40 24 48 112), lower := (rows 7 11 84 40 24 32 64), losses := [{ target := 3, region := (rows 1 2 20 0 16 52 84), good := (rows 103 3 116 32 116 32 64) }] }

theorem profile41_node9 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,8] 6 48 profile41_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,8] 6 48 profile41_node9_cert).mp (by decide +kernel))

def profile41_node10_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 11 84 40 48 56 88), lower := (rows 7 11 84 40 48 32 64), losses := [{ target := 4, region := (rows 5 6 4 56 0 32 64), good := (rows 7 11 79 40 40 40 64) }] }

theorem profile41_node10 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,32] 6 24 profile41_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32,32] 6 24 profile41_node10_cert).mp (by decide +kernel))

def profile41_node8_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node8_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node8 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80,32] 6 (by decide) (choices 1) [8,32] profile41_node8_route profile41_node8_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node9
  · exact profile41_node10

def profile41_node6_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node6 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9,80] 6 (by decide) (choices 1) [16,32] profile41_node6_route profile41_node6_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node7
  · exact profile41_node8

def profile41_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile41_node2_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node2 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,9] 6 (by decide) (choices 2) [24,48,72,80] profile41_node2_route profile41_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node3
  · exact profile41_node4
  · exact profile41_node5
  · exact profile41_node6

def profile41_node12_cert : Bound 7 := { allowed := (rows 56 32 48 0 0 0 0), upper := (rows 7 26 13 120 112 112 112), lower := (rows 7 26 13 8 16 32 64), losses := [] }

theorem profile41_node12 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,9] 6 112 profile41_node12_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,9] 6 112 profile41_node12_cert).mp (by decide +kernel))

def profile41_node13_cert : Bound 7 := { allowed := (rows 56 32 32 0 0 0 0), upper := (rows 7 26 28 105 113 97 97), lower := (rows 7 26 28 8 16 32 64), losses := [] }

theorem profile41_node13 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,24] 6 97 profile41_node13_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,24] 6 97 profile41_node13_cert).mp (by decide +kernel))

def profile41_node14_cert : Bound 7 := { allowed := (rows 56 32 24 0 0 0 0), upper := (rows 7 26 37 120 120 120 120), lower := (rows 7 26 37 8 16 32 64), losses := [] }

theorem profile41_node14 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,33] 6 120 profile41_node14_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,33] 6 120 profile41_node14_cert).mp (by decide +kernel))

def profile41_node15_cert : Bound 7 := { allowed := (rows 56 32 16 0 0 0 0), upper := (rows 7 26 44 121 113 113 113), lower := (rows 7 26 44 8 16 32 64), losses := [] }

theorem profile41_node15 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,40] 6 113 profile41_node15_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,40] 6 113 profile41_node15_cert).mp (by decide +kernel))

def profile41_node17_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 69 24 56 40 104), lower := (rows 7 26 69 24 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 42 74), good := (rows 103 111 69 104 0 32 64) }] }

theorem profile41_node17 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,16] 6 40 profile41_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,16] 6 40 profile41_node17_cert).mp (by decide +kernel))

def profile41_node19_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 7 26 69 40 24 48 112), lower := (rows 7 26 69 40 24 32 64), losses := [{ target := 3, region := (rows 3 2 7 0 16 50 82), good := (rows 103 119 69 32 112 32 64) }] }

theorem profile41_node19 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,8] 6 48 profile41_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,8] 6 48 profile41_node19_cert).mp (by decide +kernel))

def profile41_node20_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 7 26 69 40 48 56 88), lower := (rows 7 26 69 40 48 32 64), losses := [{ target := 5, region := (rows 3 2 7 8 16 0 66), good := (rows 71 95 69 8 16 0 64) }] }

theorem profile41_node20 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,32] 6 24 profile41_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32,32] 6 24 profile41_node20_cert).mp (by decide +kernel))

def profile41_node18_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node18 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65,32] 6 (by decide) (choices 1) [8,32] profile41_node18_route profile41_node18_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node19
  · exact profile41_node20

def profile41_node16_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node16_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node16 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,65] 6 (by decide) (choices 1) [16,32] profile41_node16_route profile41_node16_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node17
  · exact profile41_node18

def profile41_node21_cert : Bound 7 := { allowed := (rows 56 32 48 0 0 0 0), upper := (rows 7 26 76 57 49 49 113), lower := (rows 7 26 76 8 16 32 64), losses := [] }

theorem profile41_node21 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,72] 6 49 profile41_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,72] 6 49 profile41_node21_cert).mp (by decide +kernel))

def profile41_node22_cert : Bound 7 := { allowed := (rows 56 32 24 0 0 0 0), upper := (rows 7 26 100 57 57 57 121), lower := (rows 7 26 100 8 16 32 64), losses := [] }

theorem profile41_node22 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,96] 6 57 profile41_node22_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24,96] 6 57 profile41_node22_cert).mp (by decide +kernel))

def profile41_node11_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile41_node11_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node11 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,24] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile41_node11_route profile41_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node12
  · exact profile41_node13
  · exact profile41_node14
  · exact profile41_node15
  · exact profile41_node16
  · exact profile41_node21
  · exact profile41_node22

def profile41_node25_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 67 28 24 56 40 104), lower := (rows 7 67 28 24 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 44 76), good := (rows 103 67 111 104 0 32 64) }] }

theorem profile41_node25 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,16] 6 40 profile41_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,16] 6 40 profile41_node25_cert).mp (by decide +kernel))

def profile41_node27_cert : CutBound 7 := { lost := (rows 8 8 0 0 0 0 0), upper := (rows 7 67 28 40 24 48 112), lower := (rows 7 67 28 40 24 32 64), losses := [{ target := 3, region := (rows 5 7 4 0 16 52 84), good := (rows 103 67 119 32 112 32 64) }] }

theorem profile41_node27 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,8] 6 48 profile41_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,8] 6 48 profile41_node27_cert).mp (by decide +kernel))

def profile41_node28_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 7 67 28 40 48 56 88), lower := (rows 7 67 28 40 48 32 64), losses := [{ target := 5, region := (rows 5 7 4 8 16 0 68), good := (rows 71 67 95 8 16 0 64) }] }

theorem profile41_node28 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,32] 6 24 profile41_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32,32] 6 24 profile41_node28_cert).mp (by decide +kernel))

def profile41_node26_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node26 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24,32] 6 (by decide) (choices 1) [8,32] profile41_node26_route profile41_node26_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node27
  · exact profile41_node28

def profile41_node24_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node24_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node24 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65,24] 6 (by decide) (choices 1) [16,32] profile41_node24_route profile41_node24_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node25
  · exact profile41_node26

def profile41_node23_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node23_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node23 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,65] 6 (by decide) (choices 2) [24] profile41_node23_route profile41_node23_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node24

def profile41_node30_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 74 13 56 48 48 112), lower := (rows 7 74 13 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 6 8 0 32 64), good := (rows 7 79 13 8 0 32 64) }] }

theorem profile41_node30 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,9] 6 48 profile41_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,9] 6 48 profile41_node30_cert).mp (by decide +kernel))

def profile41_node32_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 7 74 21 24 56 40 104), lower := (rows 7 74 21 24 16 32 64), losses := [{ target := 4, region := (rows 1 10 4 8 0 42 74), good := (rows 103 106 5 106 0 32 64) }] }

theorem profile41_node32 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,16] 6 40 profile41_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,16] 6 40 profile41_node32_cert).mp (by decide +kernel))

def profile41_node34_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 7 74 21 40 24 48 112), lower := (rows 7 74 21 40 24 32 64), losses := [{ target := 5, region := (rows 3 2 7 8 26 0 64), good := (rows 23 95 21 24 24 0 64) }] }

theorem profile41_node34 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,8] 6 48 profile41_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,8] 6 48 profile41_node34_cert).mp (by decide +kernel))

def profile41_node35_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 7 74 21 40 48 56 88), lower := (rows 7 74 21 40 48 32 64), losses := [{ target := 3, region := (rows 3 2 6 0 56 32 64), good := (rows 7 87 21 48 48 48 64) }] }

theorem profile41_node35 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,32] 6 24 profile41_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32,32] 6 24 profile41_node35_cert).mp (by decide +kernel))

def profile41_node33_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node33 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17,32] 6 (by decide) (choices 1) [8,32] profile41_node33_route profile41_node33_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node34
  · exact profile41_node35

def profile41_node31_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node31_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node31 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,17] 6 (by decide) (choices 1) [16,32] profile41_node31_route profile41_node31_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node32
  · exact profile41_node33

def profile41_node36_cert : Bound 7 := { allowed := (rows 56 48 32 0 0 0 0), upper := (rows 7 74 28 57 49 49 113), lower := (rows 7 74 28 8 16 32 64), losses := [] }

theorem profile41_node36 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,24] 6 49 profile41_node36_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,24] 6 49 profile41_node36_cert).mp (by decide +kernel))

def profile41_node37_cert : Bound 7 := { allowed := (rows 56 48 8 0 0 0 0), upper := (rows 7 74 52 57 57 57 121), lower := (rows 7 74 52 8 16 32 64), losses := [] }

theorem profile41_node37 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,48] 6 57 profile41_node37_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72,48] 6 57 profile41_node37_cert).mp (by decide +kernel))

def profile41_node29_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node29_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node29 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6,72] 6 (by decide) (choices 2) [9,17,24,48] profile41_node29_route profile41_node29_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node30
  · exact profile41_node31
  · exact profile41_node36
  · exact profile41_node37

def profile41_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile41_node1_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node1 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [6] 6 (by decide) (choices 2) [9,24,65,72] profile41_node1_route profile41_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node2
  · exact profile41_node11
  · exact profile41_node23
  · exact profile41_node29

def profile41_node40_cert : Bound 7 := { allowed := (rows 48 56 32 0 0 0 0), upper := (rows 11 7 28 120 112 112 112), lower := (rows 11 7 28 8 16 32 64), losses := [] }

theorem profile41_node40 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,24] 6 112 profile41_node40_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,24] 6 112 profile41_node40_cert).mp (by decide +kernel))

def profile41_node41_cert : Bound 7 := { allowed := (rows 48 56 8 0 0 0 0), upper := (rows 11 7 52 120 120 120 120), lower := (rows 11 7 52 8 16 32 64), losses := [] }

theorem profile41_node41 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,48] 6 120 profile41_node41_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,48] 6 120 profile41_node41_cert).mp (by decide +kernel))

def profile41_node42_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 11 7 76 56 48 48 112), lower := (rows 11 7 76 8 16 32 64), losses := [{ target := 4, region := (rows 5 6 4 8 0 32 64), good := (rows 11 7 79 8 0 32 64) }] }

theorem profile41_node42 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,72] 6 48 profile41_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,72] 6 48 profile41_node42_cert).mp (by decide +kernel))

def profile41_node44_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 11 7 84 24 56 40 104), lower := (rows 11 7 84 24 16 32 64), losses := [{ target := 5, region := (rows 7 6 4 28 16 0 64), good := (rows 11 15 95 24 24 0 64) }] }

theorem profile41_node44 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,16] 6 40 profile41_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,16] 6 40 profile41_node44_cert).mp (by decide +kernel))

def profile41_node46_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 7 84 40 24 48 112), lower := (rows 11 7 84 40 24 32 64), losses := [{ target := 3, region := (rows 1 2 20 0 16 52 84), good := (rows 3 103 116 32 116 32 64) }] }

theorem profile41_node46 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,8] 6 48 profile41_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,8] 6 48 profile41_node46_cert).mp (by decide +kernel))

def profile41_node47_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 11 7 84 40 48 56 88), lower := (rows 11 7 84 40 48 32 64), losses := [{ target := 4, region := (rows 5 6 4 56 0 32 64), good := (rows 11 7 79 40 40 40 64) }] }

theorem profile41_node47 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,32] 6 24 profile41_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32,32] 6 24 profile41_node47_cert).mp (by decide +kernel))

def profile41_node45_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node45_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node45 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80,32] 6 (by decide) (choices 1) [8,32] profile41_node45_route profile41_node45_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node46
  · exact profile41_node47

def profile41_node43_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node43_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node43 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5,80] 6 (by decide) (choices 1) [16,32] profile41_node43_route profile41_node43_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node44
  · exact profile41_node45

def profile41_node39_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile41_node39_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node39 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,5] 6 (by decide) (choices 2) [24,48,72,80] profile41_node39_route profile41_node39_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node40
  · exact profile41_node41
  · exact profile41_node42
  · exact profile41_node43

def profile41_node48_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 11 116 124 116 116 116), lower := (rows 11 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 119 119 116 116 116 116 116) }] }

theorem profile41_node48 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,9] 6 116 profile41_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,9] 6 116 profile41_node48_cert).mp (by decide +kernel))

def profile41_node49_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 14 117 121 113 113 113), lower := (rows 11 14 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 119 6 4 0 16 32 64) }] }

theorem profile41_node49 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,12] 6 113 profile41_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,12] 6 113 profile41_node49_cert).mp (by decide +kernel))

def profile41_node51_cert : Bound 7 := { allowed := (rows 48 40 32 0 0 0 0), upper := (rows 11 19 28 108 116 100 100), lower := (rows 11 19 28 8 16 32 64), losses := [] }

theorem profile41_node51 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,24] 6 100 profile41_node51_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,24] 6 100 profile41_node51_cert).mp (by decide +kernel))

def profile41_node52_cert : Bound 7 := { allowed := (rows 48 40 16 0 0 0 0), upper := (rows 11 19 44 124 116 116 116), lower := (rows 11 19 44 8 16 32 64), losses := [] }

theorem profile41_node52 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,40] 6 116 profile41_node52_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,40] 6 116 profile41_node52_cert).mp (by decide +kernel))

def profile41_node53_cert : Bound 7 := { allowed := (rows 48 40 8 0 0 0 0), upper := (rows 11 19 52 108 124 108 108), lower := (rows 11 19 52 8 16 32 64), losses := [] }

theorem profile41_node53 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,48] 6 108 profile41_node53_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,48] 6 108 profile41_node53_cert).mp (by decide +kernel))

def profile41_node54_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 11 19 76 60 52 52 116), lower := (rows 11 19 76 8 16 32 64), losses := [] }

theorem profile41_node54 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,72] 6 52 profile41_node54_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,72] 6 52 profile41_node54_cert).mp (by decide +kernel))

def profile41_node55_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 11 19 84 44 60 44 108), lower := (rows 11 19 84 8 16 32 64), losses := [] }

theorem profile41_node55 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,80] 6 44 profile41_node55_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,80] 6 44 profile41_node55_cert).mp (by decide +kernel))

def profile41_node56_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 11 19 100 60 60 60 124), lower := (rows 11 19 100 8 16 32 64), losses := [] }

theorem profile41_node56 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,96] 6 60 profile41_node56_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17,96] 6 60 profile41_node56_cert).mp (by decide +kernel))

def profile41_node50_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile41_node50_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node50 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,17] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile41_node50_route profile41_node50_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node51
  · exact profile41_node52
  · exact profile41_node53
  · exact profile41_node54
  · exact profile41_node55
  · exact profile41_node56

def profile41_node58_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 11 22 13 120 112 112 112), lower := (rows 11 22 13 8 16 32 64), losses := [] }

theorem profile41_node58 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,9] 6 112 profile41_node58_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,9] 6 112 profile41_node58_cert).mp (by decide +kernel))

def profile41_node59_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 11 22 21 104 120 104 104), lower := (rows 11 22 21 8 16 32 64), losses := [] }

theorem profile41_node59 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,17] 6 104 profile41_node59_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,17] 6 104 profile41_node59_cert).mp (by decide +kernel))

def profile41_node60_cert : Bound 7 := { allowed := (rows 48 40 32 0 0 0 0), upper := (rows 11 22 28 105 113 97 97), lower := (rows 11 22 28 8 16 32 64), losses := [] }

theorem profile41_node60 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,24] 6 97 profile41_node60_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,24] 6 97 profile41_node60_cert).mp (by decide +kernel))

def profile41_node61_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 11 22 37 120 120 120 120), lower := (rows 11 22 37 8 16 32 64), losses := [] }

theorem profile41_node61 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,33] 6 120 profile41_node61_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,33] 6 120 profile41_node61_cert).mp (by decide +kernel))

def profile41_node62_cert : Bound 7 := { allowed := (rows 48 40 16 0 0 0 0), upper := (rows 11 22 44 121 113 113 113), lower := (rows 11 22 44 8 16 32 64), losses := [] }

theorem profile41_node62 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,40] 6 113 profile41_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,40] 6 113 profile41_node62_cert).mp (by decide +kernel))

def profile41_node63_cert : Bound 7 := { allowed := (rows 48 40 8 0 0 0 0), upper := (rows 11 22 52 105 121 105 105), lower := (rows 11 22 52 8 16 32 64), losses := [] }

theorem profile41_node63 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,48] 6 105 profile41_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,48] 6 105 profile41_node63_cert).mp (by decide +kernel))

def profile41_node65_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 11 22 69 24 56 40 104), lower := (rows 11 22 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 41 73), good := (rows 111 6 101 104 0 32 64) }] }

theorem profile41_node65 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,16] 6 40 profile41_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,16] 6 40 profile41_node65_cert).mp (by decide +kernel))

def profile41_node67_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 22 69 40 24 48 112), lower := (rows 11 22 69 40 24 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 50 82), good := (rows 103 118 69 32 112 32 64) }] }

theorem profile41_node67 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,8] 6 48 profile41_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,8] 6 48 profile41_node67_cert).mp (by decide +kernel))

def profile41_node68_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 11 22 69 40 48 56 88), lower := (rows 11 22 69 40 48 32 64), losses := [{ target := 4, region := (rows 3 2 4 56 0 32 64), good := (rows 11 15 69 40 40 40 64) }] }

theorem profile41_node68 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,32] 6 24 profile41_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32,32] 6 24 profile41_node68_cert).mp (by decide +kernel))

def profile41_node66_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node66_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node66 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65,32] 6 (by decide) (choices 1) [8,32] profile41_node66_route profile41_node66_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node67
  · exact profile41_node68

def profile41_node64_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node64_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node64 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,65] 6 (by decide) (choices 1) [16,32] profile41_node64_route profile41_node64_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node65
  · exact profile41_node66

def profile41_node69_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 11 22 76 57 49 49 113), lower := (rows 11 22 76 8 16 32 64), losses := [] }

theorem profile41_node69 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,72] 6 49 profile41_node69_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,72] 6 49 profile41_node69_cert).mp (by decide +kernel))

def profile41_node70_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 11 22 84 41 57 41 105), lower := (rows 11 22 84 8 16 32 64), losses := [] }

theorem profile41_node70 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,80] 6 41 profile41_node70_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,80] 6 41 profile41_node70_cert).mp (by decide +kernel))

def profile41_node71_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 11 22 100 57 57 57 121), lower := (rows 11 22 100 8 16 32 64), losses := [] }

theorem profile41_node71 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,96] 6 57 profile41_node71_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20,96] 6 57 profile41_node71_cert).mp (by decide +kernel))

def profile41_node57_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile41_node57_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node57 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,20] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile41_node57_route profile41_node57_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node58
  · exact profile41_node59
  · exact profile41_node60
  · exact profile41_node61
  · exact profile41_node62
  · exact profile41_node63
  · exact profile41_node64
  · exact profile41_node69
  · exact profile41_node70
  · exact profile41_node71

def profile41_node72_cert : Bound 7 := { allowed := (rows 48 32 56 0 0 0 0), upper := (rows 11 26 117 125 117 117 117), lower := (rows 11 26 4 8 16 32 64), losses := [] }

theorem profile41_node72 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,24] 6 117 profile41_node72_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,24] 6 117 profile41_node72_cert).mp (by decide +kernel))

def profile41_node73_cert : Bound 7 := { allowed := (rows 48 8 56 0 0 0 0), upper := (rows 11 50 125 125 125 125 125), lower := (rows 11 50 4 8 16 32 64), losses := [] }

theorem profile41_node73 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,48] 6 125 profile41_node73_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,48] 6 125 profile41_node73_cert).mp (by decide +kernel))

def profile41_node75_cert : Bound 7 := { allowed := (rows 48 56 32 0 0 0 0), upper := (rows 11 67 28 60 52 52 116), lower := (rows 11 67 28 8 16 32 64), losses := [] }

theorem profile41_node75 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,24] 6 52 profile41_node75_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,24] 6 52 profile41_node75_cert).mp (by decide +kernel))

def profile41_node76_cert : Bound 7 := { allowed := (rows 48 56 8 0 0 0 0), upper := (rows 11 67 52 60 60 60 124), lower := (rows 11 67 52 8 16 32 64), losses := [] }

theorem profile41_node76 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,48] 6 60 profile41_node76_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65,48] 6 60 profile41_node76_cert).mp (by decide +kernel))

def profile41_node74_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node74_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node74 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,65] 6 (by decide) (choices 2) [24,48] profile41_node74_route profile41_node74_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node75
  · exact profile41_node76

def profile41_node78_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 70 13 56 48 48 112), lower := (rows 11 70 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 4 0 127 127 127), good := (rows 115 118 119 112 112 112 112) }] }

theorem profile41_node78 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,9] 6 48 profile41_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,9] 6 48 profile41_node78_cert).mp (by decide +kernel))

def profile41_node80_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 11 70 21 24 56 40 104), lower := (rows 11 70 21 24 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 41 73), good := (rows 107 70 103 104 0 32 64) }] }

theorem profile41_node80 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,16] 6 40 profile41_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,16] 6 40 profile41_node80_cert).mp (by decide +kernel))

def profile41_node82_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 70 21 40 24 48 112), lower := (rows 11 70 21 40 24 32 64), losses := [{ target := 3, region := (rows 1 6 4 0 16 52 84), good := (rows 3 102 119 32 112 32 64) }] }

theorem profile41_node82 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,8] 6 48 profile41_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,8] 6 48 profile41_node82_cert).mp (by decide +kernel))

def profile41_node83_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 70 21 40 48 56 88), lower := (rows 11 70 21 40 48 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 56 32 64), good := (rows 23 70 21 48 48 48 64) }] }

theorem profile41_node83 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,32] 6 24 profile41_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32,32] 6 24 profile41_node83_cert).mp (by decide +kernel))

def profile41_node81_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node81_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node81 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17,32] 6 (by decide) (choices 1) [8,32] profile41_node81_route profile41_node81_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node82
  · exact profile41_node83

def profile41_node79_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node79_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node79 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,17] 6 (by decide) (choices 1) [16,32] profile41_node79_route profile41_node79_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node80
  · exact profile41_node81

def profile41_node84_cert : Bound 7 := { allowed := (rows 48 56 32 0 0 0 0), upper := (rows 11 70 28 57 49 49 113), lower := (rows 11 70 28 8 16 32 64), losses := [] }

theorem profile41_node84 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,24] 6 49 profile41_node84_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,24] 6 49 profile41_node84_cert).mp (by decide +kernel))

def profile41_node85_cert : Bound 7 := { allowed := (rows 48 56 8 0 0 0 0), upper := (rows 11 70 52 57 57 57 121), lower := (rows 11 70 52 8 16 32 64), losses := [] }

theorem profile41_node85 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,48] 6 57 profile41_node85_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68,48] 6 57 profile41_node85_cert).mp (by decide +kernel))

def profile41_node77_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node77_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node77 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,68] 6 (by decide) (choices 2) [9,17,24,48] profile41_node77_route profile41_node77_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node78
  · exact profile41_node79
  · exact profile41_node84
  · exact profile41_node85

def profile41_node86_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 74 53 61 53 53 117), lower := (rows 11 74 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 119 66 4 0 16 32 64) }] }

theorem profile41_node86 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,72] 6 53 profile41_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,72] 6 53 profile41_node86_cert).mp (by decide +kernel))

def profile41_node88_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 11 82 13 60 52 52 116), lower := (rows 11 82 13 8 16 32 64), losses := [] }

theorem profile41_node88 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,9] 6 52 profile41_node88_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,9] 6 52 profile41_node88_cert).mp (by decide +kernel))

def profile41_node89_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 11 82 21 44 60 44 108), lower := (rows 11 82 21 8 16 32 64), losses := [] }

theorem profile41_node89 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,17] 6 44 profile41_node89_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,17] 6 44 profile41_node89_cert).mp (by decide +kernel))

def profile41_node90_cert : Bound 7 := { allowed := (rows 48 40 32 0 0 0 0), upper := (rows 11 82 28 45 53 37 101), lower := (rows 11 82 28 8 16 32 64), losses := [] }

theorem profile41_node90 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,24] 6 37 profile41_node90_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,24] 6 37 profile41_node90_cert).mp (by decide +kernel))

def profile41_node91_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 11 82 37 60 60 60 124), lower := (rows 11 82 37 8 16 32 64), losses := [] }

theorem profile41_node91 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,33] 6 60 profile41_node91_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,33] 6 60 profile41_node91_cert).mp (by decide +kernel))

def profile41_node92_cert : Bound 7 := { allowed := (rows 48 40 16 0 0 0 0), upper := (rows 11 82 44 61 53 53 117), lower := (rows 11 82 44 8 16 32 64), losses := [] }

theorem profile41_node92 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,40] 6 53 profile41_node92_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,40] 6 53 profile41_node92_cert).mp (by decide +kernel))

def profile41_node93_cert : Bound 7 := { allowed := (rows 48 40 8 0 0 0 0), upper := (rows 11 82 52 45 61 45 109), lower := (rows 11 82 52 8 16 32 64), losses := [] }

theorem profile41_node93 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,48] 6 45 profile41_node93_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80,48] 6 45 profile41_node93_cert).mp (by decide +kernel))

def profile41_node87_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node87_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node87 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10,80] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile41_node87_route profile41_node87_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node88
  · exact profile41_node89
  · exact profile41_node90
  · exact profile41_node91
  · exact profile41_node92
  · exact profile41_node93

def profile41_node38_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile41_node38_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node38 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [10] 6 (by decide) (choices 2) [5,9,12,17,20,24,48,65,68,72,80] profile41_node38_route profile41_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node39
  · exact profile41_node48
  · exact profile41_node49
  · exact profile41_node50
  · exact profile41_node57
  · exact profile41_node72
  · exact profile41_node73
  · exact profile41_node74
  · exact profile41_node77
  · exact profile41_node86
  · exact profile41_node87

def profile41_node96_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 7 14 120 112 112 112), lower := (rows 25 7 14 8 16 32 64), losses := [] }

theorem profile41_node96 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,10] 6 112 profile41_node96_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,10] 6 112 profile41_node96_cert).mp (by decide +kernel))

def profile41_node97_cert : Bound 7 := { allowed := (rows 32 56 32 0 0 0 0), upper := (rows 25 7 28 106 114 98 98), lower := (rows 25 7 28 8 16 32 64), losses := [] }

theorem profile41_node97 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,24] 6 98 profile41_node97_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,24] 6 98 profile41_node97_cert).mp (by decide +kernel))

def profile41_node98_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 7 38 120 120 120 120), lower := (rows 25 7 38 8 16 32 64), losses := [] }

theorem profile41_node98 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,34] 6 120 profile41_node98_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,34] 6 120 profile41_node98_cert).mp (by decide +kernel))

def profile41_node99_cert : Bound 7 := { allowed := (rows 32 56 16 0 0 0 0), upper := (rows 25 7 44 122 114 114 114), lower := (rows 25 7 44 8 16 32 64), losses := [] }

theorem profile41_node99 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,40] 6 114 profile41_node99_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,40] 6 114 profile41_node99_cert).mp (by decide +kernel))

def profile41_node101_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 7 70 24 56 40 104), lower := (rows 25 7 70 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 41 73), good := (rows 111 103 70 104 0 32 64) }] }

theorem profile41_node101 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,16] 6 40 profile41_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,16] 6 40 profile41_node101_cert).mp (by decide +kernel))

def profile41_node103_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 25 7 70 40 24 48 112), lower := (rows 25 7 70 40 24 32 64), losses := [{ target := 3, region := (rows 1 3 7 0 16 49 81), good := (rows 119 103 70 32 112 32 64) }] }

theorem profile41_node103 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,8] 6 48 profile41_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,8] 6 48 profile41_node103_cert).mp (by decide +kernel))

def profile41_node104_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 25 7 70 40 48 56 88), lower := (rows 25 7 70 40 48 32 64), losses := [{ target := 5, region := (rows 1 3 7 8 16 0 65), good := (rows 95 71 70 8 16 0 64) }] }

theorem profile41_node104 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,32] 6 24 profile41_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32,32] 6 24 profile41_node104_cert).mp (by decide +kernel))

def profile41_node102_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node102_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node102 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66,32] 6 (by decide) (choices 1) [8,32] profile41_node102_route profile41_node102_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node103
  · exact profile41_node104

def profile41_node100_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node100_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node100 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,66] 6 (by decide) (choices 1) [16,32] profile41_node100_route profile41_node100_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node101
  · exact profile41_node102

def profile41_node105_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 7 76 58 50 50 114), lower := (rows 25 7 76 8 16 32 64), losses := [] }

theorem profile41_node105 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,72] 6 50 profile41_node105_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,72] 6 50 profile41_node105_cert).mp (by decide +kernel))

def profile41_node106_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 7 100 58 58 58 122), lower := (rows 25 7 100 8 16 32 64), losses := [] }

theorem profile41_node106 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,96] 6 58 profile41_node106_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5,96] 6 58 profile41_node106_cert).mp (by decide +kernel))

def profile41_node95_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile41_node95_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node95 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,5] 6 (by decide) (choices 2) [10,24,34,40,66,72,96] profile41_node95_route profile41_node95_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node96
  · exact profile41_node97
  · exact profile41_node98
  · exact profile41_node99
  · exact profile41_node100
  · exact profile41_node105
  · exact profile41_node106

def profile41_node107_cert : Bound 7 := { allowed := (rows 32 48 56 0 0 0 0), upper := (rows 25 11 118 126 118 118 118), lower := (rows 25 11 4 8 16 32 64), losses := [] }

theorem profile41_node107 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,9] 6 118 profile41_node107_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,9] 6 118 profile41_node107_cert).mp (by decide +kernel))

def profile41_node108_cert : Bound 7 := { allowed := (rows 32 48 56 0 0 0 0), upper := (rows 25 14 119 123 115 115 115), lower := (rows 25 14 4 8 16 32 64), losses := [] }

theorem profile41_node108 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,12] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,12] 6 115 profile41_node108_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,12] 6 115 profile41_node108_cert).mp (by decide +kernel))

def profile41_node109_cert : Bound 7 := { allowed := (rows 32 32 56 0 0 0 0), upper := (rows 25 26 103 111 119 103 103), lower := (rows 25 26 4 8 16 32 64), losses := [] }

theorem profile41_node109 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,24] 6 103 profile41_node109_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,24] 6 103 profile41_node109_cert).mp (by decide +kernel))

def profile41_node110_cert : Bound 7 := { allowed := (rows 32 24 56 0 0 0 0), upper := (rows 25 35 126 126 126 126 126), lower := (rows 25 35 4 8 16 32 64), losses := [] }

theorem profile41_node110 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,33] 6 126 profile41_node110_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,33] 6 126 profile41_node110_cert).mp (by decide +kernel))

def profile41_node111_cert : Bound 7 := { allowed := (rows 32 24 56 0 0 0 0), upper := (rows 25 38 127 123 123 123 123), lower := (rows 25 38 4 8 16 32 64), losses := [] }

theorem profile41_node111 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,36] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,36] 6 123 profile41_node111_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,36] 6 123 profile41_node111_cert).mp (by decide +kernel))

def profile41_node112_cert : Bound 7 := { allowed := (rows 32 16 56 0 0 0 0), upper := (rows 25 42 119 127 119 119 119), lower := (rows 25 42 4 8 16 32 64), losses := [] }

theorem profile41_node112 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,40] 6 119 profile41_node112_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,40] 6 119 profile41_node112_cert).mp (by decide +kernel))

def profile41_node114_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 67 14 60 52 52 116), lower := (rows 25 67 14 8 16 32 64), losses := [] }

theorem profile41_node114 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,10] 6 52 profile41_node114_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,10] 6 52 profile41_node114_cert).mp (by decide +kernel))

def profile41_node115_cert : Bound 7 := { allowed := (rows 32 56 32 0 0 0 0), upper := (rows 25 67 28 46 54 38 102), lower := (rows 25 67 28 8 16 32 64), losses := [] }

theorem profile41_node115 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,24] 6 38 profile41_node115_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,24] 6 38 profile41_node115_cert).mp (by decide +kernel))

def profile41_node116_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 67 38 60 60 60 124), lower := (rows 25 67 38 8 16 32 64), losses := [] }

theorem profile41_node116 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,34] 6 60 profile41_node116_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,34] 6 60 profile41_node116_cert).mp (by decide +kernel))

def profile41_node117_cert : Bound 7 := { allowed := (rows 32 56 16 0 0 0 0), upper := (rows 25 67 44 62 54 54 118), lower := (rows 25 67 44 8 16 32 64), losses := [] }

theorem profile41_node117 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,40] 6 54 profile41_node117_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65,40] 6 54 profile41_node117_cert).mp (by decide +kernel))

def profile41_node113_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node113_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node113 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,65] 6 (by decide) (choices 2) [10,24,34,40] profile41_node113_route profile41_node113_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node114
  · exact profile41_node115
  · exact profile41_node116
  · exact profile41_node117

def profile41_node120_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 70 7 24 56 40 104), lower := (rows 25 70 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 8 0 41 73), good := (rows 111 70 103 104 0 32 64) }] }

theorem profile41_node120 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,16] 6 40 profile41_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,16] 6 40 profile41_node120_cert).mp (by decide +kernel))

def profile41_node122_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 25 70 7 40 24 48 112), lower := (rows 25 70 7 40 24 32 64), losses := [{ target := 3, region := (rows 1 7 5 0 16 49 81), good := (rows 119 70 103 32 112 32 64) }] }

theorem profile41_node122 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,8] 6 48 profile41_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,8] 6 48 profile41_node122_cert).mp (by decide +kernel))

def profile41_node123_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 25 70 7 40 48 56 88), lower := (rows 25 70 7 40 48 32 64), losses := [{ target := 5, region := (rows 1 7 5 8 16 0 65), good := (rows 95 70 71 8 16 0 64) }] }

theorem profile41_node123 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,32] 6 24 profile41_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32,32] 6 24 profile41_node123_cert).mp (by decide +kernel))

def profile41_node121_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node121_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node121 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3,32] 6 (by decide) (choices 1) [8,32] profile41_node121_route profile41_node121_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node122
  · exact profile41_node123

def profile41_node119_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node119_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node119 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,3] 6 (by decide) (choices 1) [16,32] profile41_node119_route profile41_node119_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node120
  · exact profile41_node121

def profile41_node124_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 70 13 58 50 50 114), lower := (rows 25 70 13 8 16 32 64), losses := [] }

theorem profile41_node124 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,9] 6 50 profile41_node124_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,9] 6 50 profile41_node124_cert).mp (by decide +kernel))

def profile41_node125_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 70 14 57 49 49 113), lower := (rows 25 70 14 8 16 32 64), losses := [] }

theorem profile41_node125 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,10] 6 49 profile41_node125_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,10] 6 49 profile41_node125_cert).mp (by decide +kernel))

def profile41_node126_cert : Bound 7 := { allowed := (rows 32 56 32 0 0 0 0), upper := (rows 25 70 28 43 51 35 99), lower := (rows 25 70 28 8 16 32 64), losses := [] }

theorem profile41_node126 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,24] 6 35 profile41_node126_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,24] 6 35 profile41_node126_cert).mp (by decide +kernel))

def profile41_node127_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 70 37 58 58 58 122), lower := (rows 25 70 37 8 16 32 64), losses := [] }

theorem profile41_node127 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,33] 6 58 profile41_node127_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,33] 6 58 profile41_node127_cert).mp (by decide +kernel))

def profile41_node128_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 70 38 57 57 57 121), lower := (rows 25 70 38 8 16 32 64), losses := [] }

theorem profile41_node128 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,34] 6 57 profile41_node128_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,34] 6 57 profile41_node128_cert).mp (by decide +kernel))

def profile41_node129_cert : Bound 7 := { allowed := (rows 32 56 16 0 0 0 0), upper := (rows 25 70 44 59 51 51 115), lower := (rows 25 70 44 8 16 32 64), losses := [] }

theorem profile41_node129 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,40] 6 51 profile41_node129_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68,40] 6 51 profile41_node129_cert).mp (by decide +kernel))

def profile41_node118_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node118_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node118 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,68] 6 (by decide) (choices 2) [3,9,10,24,33,34,40] profile41_node118_route profile41_node118_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node119
  · exact profile41_node124
  · exact profile41_node125
  · exact profile41_node126
  · exact profile41_node127
  · exact profile41_node128
  · exact profile41_node129


#print axioms profile41_node118
end Delivery.SmallBudgetTenFinite7
