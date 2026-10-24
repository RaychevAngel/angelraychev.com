import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile34_node4_cert : CutBound 7 := { lost := (rows 64 64 64 64 0 0 0), upper := (rows 7 11 52 56 80 96 64), lower := (rows 7 11 52 56 16 32 64), losses := [{ target := 6, region := (rows 15 15 12 12 16 32 0), good := (rows 15 15 63 63 16 32 0) }] }

theorem profile34_node4 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,48] 6 64 profile34_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,48] 6 64 profile34_node4_cert).mp (by decide +kernel))

def profile34_node5_cert : CutBound 7 := { lost := (rows 32 32 0 32 0 0 0), upper := (rows 7 11 52 88 112 96 64), lower := (rows 7 11 52 88 16 32 64), losses := [{ target := 5, region := (rows 5 7 4 28 16 0 127), good := (rows 79 75 95 88 88 64 64) }] }

theorem profile34_node5 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,80] 6 96 profile34_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48,80] 6 96 profile34_node5_cert).mp (by decide +kernel))

def profile34_node3_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node3_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node3 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,48] 6 (by decide) (choices 2) [48,80] profile34_node3_route profile34_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node4
  · exact profile34_node5

def profile34_node7_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 7 11 84 56 112 96 64), lower := (rows 7 11 84 56 16 32 64), losses := [{ target := 5, region := (rows 11 10 28 8 16 0 127), good := (rows 71 79 84 95 84 64 64) }] }

theorem profile34_node7 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,48] 6 96 profile34_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,48] 6 96 profile34_node7_cert).mp (by decide +kernel))

def profile34_node8_cert : CutBound 7 := { lost := (rows 32 32 32 32 0 0 0), upper := (rows 7 11 84 88 48 32 64), lower := (rows 7 11 84 88 16 32 64), losses := [{ target := 5, region := (rows 31 31 28 28 16 0 127), good := (rows 79 79 95 95 95 64 64) }] }

theorem profile34_node8 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,80] 6 32 profile34_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,80] 6 32 profile34_node8_cert).mp (by decide +kernel))

def profile34_node9_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 7 11 84 104 48 48 64), lower := (rows 7 11 84 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 127), good := (rows 71 75 68 104 64 104 64) },{ target := 5, region := (rows 1 2 20 8 16 0 127), good := (rows 71 75 84 72 84 64 64) }] }

theorem profile34_node9 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,96] 6 48 profile34_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80,96] 6 48 profile34_node9_cert).mp (by decide +kernel))

def profile34_node6_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node6 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9,80] 6 (by decide) (choices 2) [48,80,96] profile34_node6_route profile34_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node7
  · exact profile34_node8
  · exact profile34_node9

def profile34_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile34_node2_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node2 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,9] 6 (by decide) (choices 2) [48,80] profile34_node2_route profile34_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node3
  · exact profile34_node6

def profile34_node11_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 7 19 28 104 112 96 64), lower := (rows 7 19 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 71 83 95 72 80 64 64) }] }

theorem profile34_node11 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,24] 6 96 profile34_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,24] 6 96 profile34_node11_cert).mp (by decide +kernel))

def profile34_node13_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 7 19 44 56 80 96 64), lower := (rows 7 19 44 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 103 99 108 108 96 96 96) },{ target := 5, region := (rows 5 7 4 8 127 0 127), good := (rows 87 83 95 88 80 80 80) }] }

theorem profile34_node13 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,48] 6 64 profile34_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,48] 6 64 profile34_node13_cert).mp (by decide +kernel))

def profile34_node14_cert : CutBound 7 := { lost := (rows 0 0 16 32 0 0 0), upper := (rows 7 19 44 88 112 96 64), lower := (rows 7 19 44 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 103 99 108 108 96 96 96) },{ target := 5, region := (rows 1 2 4 26 16 0 127), good := (rows 79 91 76 88 88 64 64) }] }

theorem profile34_node14 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,80] 6 96 profile34_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,80] 6 96 profile34_node14_cert).mp (by decide +kernel))

def profile34_node15_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 7 19 44 104 80 112 64), lower := (rows 7 19 44 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 79 67 108 108 64 108 64) }] }

theorem profile34_node15 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,96] 6 80 profile34_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40,96] 6 80 profile34_node15_cert).mp (by decide +kernel))

def profile34_node12_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node12_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node12 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,40] 6 (by decide) (choices 2) [48,80,96] profile34_node12_route profile34_node12_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node13
  · exact profile34_node14
  · exact profile34_node15

def profile34_node16_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 7 19 52 104 120 104 64), lower := (rows 7 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 71 83 87 72 80 64 64) }] }

theorem profile34_node16 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,48] 6 104 profile34_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,48] 6 104 profile34_node16_cert).mp (by decide +kernel))

def profile34_node17_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 7 19 76 120 112 112 64), lower := (rows 7 19 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 71 67 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 71 83 76 76 80 64 64) }] }

theorem profile34_node17 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,72] 6 112 profile34_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,72] 6 112 profile34_node17_cert).mp (by decide +kernel))

def profile34_node18_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 7 19 84 104 120 104 64), lower := (rows 7 19 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile34_node18 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,80] 6 104 profile34_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,80] 6 104 profile34_node18_cert).mp (by decide +kernel))

def profile34_node20_cert : Bound 7 := { allowed := (rows 112 96 0 64 0 0 0), upper := (rows 7 19 100 56 88 104 64), lower := (rows 7 19 100 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 8 0 40 127), good := (rows 71 67 100 108 64 100 64) }] }

theorem profile34_node20 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,48] 6 72 profile34_node20_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,48] 6 72 profile34_node20_cert).mp (by decide +kernel))

def profile34_node21_cert : Bound 7 := { allowed := (rows 112 96 0 32 0 0 0), upper := (rows 7 19 100 88 56 40 64), lower := (rows 7 19 100 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 8 0 40 127), good := (rows 71 67 100 108 64 100 64) }] }

theorem profile34_node21 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,80] 6 40 profile34_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,80] 6 40 profile34_node21_cert).mp (by decide +kernel))

def profile34_node22_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 7 19 100 104 24 56 64), lower := (rows 7 19 100 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 79 67 108 108 64 108 64) }] }

theorem profile34_node22 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,96] 6 24 profile34_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96,96] 6 24 profile34_node22_cert).mp (by decide +kernel))

def profile34_node19_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node19_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node19 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17,96] 6 (by decide) (choices 2) [48,80,96] profile34_node19_route profile34_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node20
  · exact profile34_node21
  · exact profile34_node22

def profile34_node10_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node10_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node10 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,17] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile34_node10_route profile34_node10_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node11
  · exact profile34_node12
  · exact profile34_node16
  · exact profile34_node17
  · exact profile34_node18
  · exact profile34_node19

def profile34_node24_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 7 26 21 104 112 96 64), lower := (rows 7 26 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 106 109 104 104 104 104) },{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 95 85 72 80 64 64) }] }

theorem profile34_node24 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,17] 6 96 profile34_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,17] 6 96 profile34_node24_cert).mp (by decide +kernel))

def profile34_node26_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 37 56 80 96 64), lower := (rows 7 26 37 56 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 111 101 104 96 96 96) }] }

theorem profile34_node26 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,48] 6 64 profile34_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,48] 6 64 profile34_node26_cert).mp (by decide +kernel))

def profile34_node27_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 37 88 112 96 64), lower := (rows 7 26 37 88 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 111 101 104 96 96 96) }] }

theorem profile34_node27 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,80] 6 96 profile34_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,80] 6 96 profile34_node27_cert).mp (by decide +kernel))

def profile34_node28_cert : CutBound 7 := { lost := (rows 0 32 0 16 0 0 0), upper := (rows 7 26 37 104 80 112 64), lower := (rows 7 26 37 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 79 74 109 104 64 104 64) },{ target := 5, region := (rows 1 10 4 8 127 0 127), good := (rows 87 90 85 90 80 80 80) }] }

theorem profile34_node28 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,96] 6 80 profile34_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33,96] 6 80 profile34_node28_cert).mp (by decide +kernel))

def profile34_node25_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node25_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node25 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,33] 6 (by decide) (choices 2) [48,80,96] profile34_node25_route profile34_node25_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node26
  · exact profile34_node27
  · exact profile34_node28

def profile34_node30_cert : CutBound 7 := { lost := (rows 0 32 0 16 0 0 0), upper := (rows 7 26 52 41 80 96 64), lower := (rows 7 26 52 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 106 100 105 96 96 96) },{ target := 5, region := (rows 1 10 4 8 127 0 127), good := (rows 87 90 84 91 80 80 80) }] }

theorem profile34_node30 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,33] 6 64 profile34_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,33] 6 64 profile34_node30_cert).mp (by decide +kernel))

def profile34_node31_cert : CutBound 7 := { lost := (rows 32 32 0 48 0 0 0), upper := (rows 7 26 52 73 112 96 64), lower := (rows 7 26 52 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 106 100 105 96 96 96) },{ target := 5, region := (rows 5 6 4 13 16 0 127), good := (rows 79 90 95 73 80 64 64) }] }

theorem profile34_node31 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,65] 6 96 profile34_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,65] 6 96 profile34_node31_cert).mp (by decide +kernel))

def profile34_node32_cert : Bound 7 := { allowed := (rows 112 96 64 0 0 0 0), upper := (rows 7 26 52 104 81 97 64), lower := (rows 7 26 52 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 45 0 33 127), good := (rows 111 74 108 104 64 104 64) }] }

theorem profile34_node32 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,96] 6 65 profile34_node32_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48,96] 6 65 profile34_node32_cert).mp (by decide +kernel))

def profile34_node29_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node29_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node29 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,48] 6 (by decide) (choices 2) [33,65,96] profile34_node29_route profile34_node29_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node30
  · exact profile34_node31
  · exact profile34_node32

def profile34_node33_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 69 120 112 112 64), lower := (rows 7 26 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 79 69 72 64 96 64) }] }

theorem profile34_node33 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,65] 6 112 profile34_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,65] 6 112 profile34_node33_cert).mp (by decide +kernel))

def profile34_node34_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 7 26 84 105 113 97 64), lower := (rows 7 26 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 74 68 72 64 96 64) },{ target := 5, region := (rows 3 2 22 8 16 0 127), good := (rows 71 95 84 72 84 64 64) }] }

theorem profile34_node34 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,80] 6 97 profile34_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,80] 6 97 profile34_node34_cert).mp (by decide +kernel))

def profile34_node36_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 100 25 112 96 64), lower := (rows 7 26 100 25 16 32 64), losses := [{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 111 100 109 100 100 100) }] }

theorem profile34_node36 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,17] 6 96 profile34_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,17] 6 96 profile34_node36_cert).mp (by decide +kernel))

def profile34_node37_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 100 41 80 112 64), lower := (rows 7 26 100 41 16 32 64), losses := [{ target := 4, region := (rows 3 2 44 8 0 32 127), good := (rows 71 79 100 109 64 100 64) }] }

theorem profile34_node37 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,33] 6 80 profile34_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,33] 6 80 profile34_node37_cert).mp (by decide +kernel))

def profile34_node38_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 100 56 81 97 64), lower := (rows 7 26 100 56 16 32 64), losses := [{ target := 4, region := (rows 3 2 47 8 0 35 127), good := (rows 103 111 100 108 64 100 64) }] }

theorem profile34_node38 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,48] 6 65 profile34_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,48] 6 65 profile34_node38_cert).mp (by decide +kernel))

def profile34_node39_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 7 26 100 73 48 48 64), lower := (rows 7 26 100 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 9 0 32 127), good := (rows 79 74 100 73 64 100 64) }] }

theorem profile34_node39 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,65] 6 48 profile34_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,65] 6 48 profile34_node39_cert).mp (by decide +kernel))

def profile34_node40_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 100 88 49 33 64), lower := (rows 7 26 100 88 16 32 64), losses := [{ target := 4, region := (rows 3 2 39 8 0 35 127), good := (rows 103 111 100 72 64 100 64) }] }

theorem profile34_node40 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,80] 6 33 profile34_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,80] 6 33 profile34_node40_cert).mp (by decide +kernel))

def profile34_node41_cert : CutBound 7 := { lost := (rows 16 0 16 16 0 0 0), upper := (rows 7 26 100 104 17 49 64), lower := (rows 7 26 100 104 16 32 64), losses := [{ target := 4, region := (rows 3 2 44 44 0 32 127), good := (rows 79 79 108 108 64 108 64) }] }

theorem profile34_node41 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,96] 6 17 profile34_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96,96] 6 17 profile34_node41_cert).mp (by decide +kernel))

def profile34_node35_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node35_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node35 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24,96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node35_route profile34_node35_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node36
  · exact profile34_node37
  · exact profile34_node38
  · exact profile34_node39
  · exact profile34_node40
  · exact profile34_node41

def profile34_node23_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile34_node23_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node23 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,24] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node23_route profile34_node23_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node24
  · exact profile34_node25
  · exact profile34_node29
  · exact profile34_node33
  · exact profile34_node34
  · exact profile34_node35

def profile34_node44_cert : CutBound 7 := { lost := (rows 64 64 64 64 0 0 0), upper := (rows 7 50 13 56 80 96 64), lower := (rows 7 50 13 56 16 32 64), losses := [{ target := 6, region := (rows 15 10 15 10 16 32 0), good := (rows 15 63 15 63 16 32 0) }] }

theorem profile34_node44 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,48] 6 64 profile34_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,48] 6 64 profile34_node44_cert).mp (by decide +kernel))

def profile34_node45_cert : CutBound 7 := { lost := (rows 32 0 32 32 0 0 0), upper := (rows 7 50 13 88 112 96 64), lower := (rows 7 50 13 88 16 32 64), losses := [{ target := 5, region := (rows 3 2 7 26 16 0 127), good := (rows 79 95 77 88 88 64 64) }] }

theorem profile34_node45 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,80] 6 96 profile34_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9,80] 6 96 profile34_node45_cert).mp (by decide +kernel))

def profile34_node43_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node43_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node43 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,9] 6 (by decide) (choices 2) [48,80] profile34_node43_route profile34_node43_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node44
  · exact profile34_node45

def profile34_node46_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 7 50 21 104 120 104 64), lower := (rows 7 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 106 109 104 104 104 104) },{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 87 85 72 80 64 64) }] }

theorem profile34_node46 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,17] 6 104 profile34_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,17] 6 104 profile34_node46_cert).mp (by decide +kernel))

def profile34_node48_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 7 50 28 41 80 96 64), lower := (rows 7 50 28 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 98 108 105 96 96 96) },{ target := 5, region := (rows 1 2 12 8 127 0 127), good := (rows 87 82 92 93 80 80 80) }] }

theorem profile34_node48 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,33] 6 64 profile34_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,33] 6 64 profile34_node48_cert).mp (by decide +kernel))

def profile34_node49_cert : CutBound 7 := { lost := (rows 32 0 32 48 0 0 0), upper := (rows 7 50 28 73 112 96 64), lower := (rows 7 50 28 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 98 108 105 96 96 96) },{ target := 5, region := (rows 3 2 6 11 16 0 127), good := (rows 79 95 92 73 80 64 64) }] }

theorem profile34_node49 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,65] 6 96 profile34_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,65] 6 96 profile34_node49_cert).mp (by decide +kernel))

def profile34_node50_cert : Bound 7 := { allowed := (rows 112 64 96 0 0 0 0), upper := (rows 7 50 28 104 81 97 64), lower := (rows 7 50 28 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 43 0 33 127), good := (rows 111 106 76 104 64 104 64) }] }

theorem profile34_node50 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,96] 6 65 profile34_node50_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24,96] 6 65 profile34_node50_cert).mp (by decide +kernel))

def profile34_node47_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node47_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node47 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,24] 6 (by decide) (choices 2) [33,65,96] profile34_node47_route profile34_node47_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node48
  · exact profile34_node49
  · exact profile34_node50

def profile34_node51_cert : CutBound 7 := { lost := (rows 0 0 0 48 0 0 0), upper := (rows 7 50 52 73 89 105 64), lower := (rows 7 50 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 100 72 64 96 64) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 82 84 72 80 64 64) }] }

theorem profile34_node51 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,48] 6 73 profile34_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,48] 6 73 profile34_node51_cert).mp (by decide +kernel))

def profile34_node52_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 50 69 120 120 120 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile34_node52 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,65] 6 120 profile34_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,65] 6 120 profile34_node52_cert).mp (by decide +kernel))

def profile34_node53_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 7 50 76 121 113 113 64), lower := (rows 7 50 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 71 98 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 71 82 76 76 80 64 64) }] }

theorem profile34_node53 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,72] 6 113 profile34_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,72] 6 113 profile34_node53_cert).mp (by decide +kernel))

def profile34_node54_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 7 50 84 105 121 105 64), lower := (rows 7 50 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 68 72 64 96 64) },{ target := 5, region := (rows 3 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile34_node54 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,80] 6 105 profile34_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48,80] 6 105 profile34_node54_cert).mp (by decide +kernel))

def profile34_node42_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node42_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node42 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,48] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile34_node42_route profile34_node42_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node43
  · exact profile34_node46
  · exact profile34_node47
  · exact profile34_node51
  · exact profile34_node52
  · exact profile34_node53
  · exact profile34_node54

def profile34_node55_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 67 124 120 120 120 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 127), good := (rows 71 67 71 72 64 96 64) }] }

theorem profile34_node55 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,65] 6 120 profile34_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,65] 6 120 profile34_node55_cert).mp (by decide +kernel))

def profile34_node56_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 7 74 117 121 113 113 64), lower := (rows 7 74 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 127), good := (rows 71 74 68 74 64 96 64) },{ target := 5, region := (rows 1 10 4 8 16 0 127), good := (rows 71 74 68 74 80 64 64) }] }

theorem profile34_node56 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,72] 6 113 profile34_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,72] 6 113 profile34_node56_cert).mp (by decide +kernel))

def profile34_node59_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 7 82 13 56 112 96 64), lower := (rows 7 82 13 56 16 32 64), losses := [{ target := 5, region := (rows 13 26 12 8 16 0 127), good := (rows 71 82 79 95 82 64 64) }] }

theorem profile34_node59 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,48] 6 96 profile34_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,48] 6 96 profile34_node59_cert).mp (by decide +kernel))

def profile34_node60_cert : CutBound 7 := { lost := (rows 32 32 32 32 0 0 0), upper := (rows 7 82 13 88 48 32 64), lower := (rows 7 82 13 88 16 32 64), losses := [{ target := 5, region := (rows 31 26 31 26 16 0 127), good := (rows 79 95 79 95 95 64 64) }] }

theorem profile34_node60 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,80] 6 32 profile34_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,80] 6 32 profile34_node60_cert).mp (by decide +kernel))

def profile34_node61_cert : CutBound 7 := { lost := (rows 0 32 0 16 0 0 0), upper := (rows 7 82 13 104 48 48 64), lower := (rows 7 82 13 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 127), good := (rows 71 66 77 104 64 104 64) },{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 71 82 77 72 82 64 64) }] }

theorem profile34_node61 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,96] 6 48 profile34_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9,96] 6 48 profile34_node61_cert).mp (by decide +kernel))

def profile34_node58_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node58_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node58 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,9] 6 (by decide) (choices 2) [48,80,96] profile34_node58_route profile34_node58_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node59
  · exact profile34_node60
  · exact profile34_node61

def profile34_node62_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 7 82 21 104 120 104 64), lower := (rows 7 82 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 106 109 104 104 104 104) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile34_node62 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,17] 6 104 profile34_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,17] 6 104 profile34_node62_cert).mp (by decide +kernel))

def profile34_node63_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 7 82 28 105 113 97 64), lower := (rows 7 82 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 76 72 64 96 64) },{ target := 5, region := (rows 5 22 4 8 16 0 127), good := (rows 71 82 95 72 82 64 64) }] }

theorem profile34_node63 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,24] 6 97 profile34_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,24] 6 97 profile34_node63_cert).mp (by decide +kernel))

def profile34_node65_cert : Bound 7 := { allowed := (rows 112 0 80 64 0 0 0), upper := (rows 7 82 37 56 88 104 64), lower := (rows 7 82 37 56 16 32 64), losses := [{ target := 5, region := (rows 1 26 4 8 24 0 127), good := (rows 71 82 69 90 82 64 64) }] }

theorem profile34_node65 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,48] 6 72 profile34_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,48] 6 72 profile34_node65_cert).mp (by decide +kernel))

def profile34_node66_cert : CutBound 7 := { lost := (rows 0 32 0 32 0 0 0), upper := (rows 7 82 37 88 56 40 64), lower := (rows 7 82 37 88 16 32 64), losses := [{ target := 5, region := (rows 1 26 4 26 16 0 127), good := (rows 79 90 69 90 90 64 64) }] }

theorem profile34_node66 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,80] 6 40 profile34_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,80] 6 40 profile34_node66_cert).mp (by decide +kernel))

def profile34_node67_cert : Bound 7 := { allowed := (rows 112 32 80 0 0 0 0), upper := (rows 7 82 37 104 24 56 64), lower := (rows 7 82 37 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 79 66 109 104 64 104 64) }] }

theorem profile34_node67 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,96] 6 24 profile34_node67_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33,96] 6 24 profile34_node67_cert).mp (by decide +kernel))

def profile34_node64_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node64_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node64 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,33] 6 (by decide) (choices 2) [48,80,96] profile34_node64_route profile34_node64_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node65
  · exact profile34_node66
  · exact profile34_node67

def profile34_node69_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 7 82 44 25 112 96 64), lower := (rows 7 82 44 25 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 103 98 108 109 96 96 96) },{ target := 5, region := (rows 5 26 4 8 16 0 127), good := (rows 71 82 79 91 82 64 64) }] }

theorem profile34_node69 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,17] 6 96 profile34_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,17] 6 96 profile34_node69_cert).mp (by decide +kernel))

def profile34_node70_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 7 82 44 41 80 112 64), lower := (rows 7 82 44 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 71 66 108 109 64 96 64) },{ target := 5, region := (rows 5 127 4 8 127 0 127), good := (rows 87 82 95 91 82 82 82) }] }

theorem profile34_node70 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,33] 6 80 profile34_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,33] 6 80 profile34_node70_cert).mp (by decide +kernel))

def profile34_node71_cert : Bound 7 := { allowed := (rows 112 32 64 64 0 0 0), upper := (rows 7 82 44 56 81 97 64), lower := (rows 7 82 44 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 33 127), good := (rows 103 66 108 108 64 96 64) }] }

theorem profile34_node71 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,48] 6 65 profile34_node71_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,48] 6 65 profile34_node71_cert).mp (by decide +kernel))

def profile34_node72_cert : CutBound 7 := { lost := (rows 0 32 0 48 0 0 0), upper := (rows 7 82 44 73 48 48 64), lower := (rows 7 82 44 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 32 127), good := (rows 79 66 108 73 64 96 64) },{ target := 5, region := (rows 1 18 4 9 16 0 127), good := (rows 79 82 76 73 82 64 64) }] }

theorem profile34_node72 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,65] 6 48 profile34_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,65] 6 48 profile34_node72_cert).mp (by decide +kernel))

def profile34_node73_cert : CutBound 7 := { lost := (rows 32 32 0 32 0 0 0), upper := (rows 7 82 44 88 49 33 64), lower := (rows 7 82 44 88 16 32 64), losses := [{ target := 5, region := (rows 5 26 4 26 16 0 127), good := (rows 79 90 79 90 90 64 64) }] }

theorem profile34_node73 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,80] 6 33 profile34_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,80] 6 33 profile34_node73_cert).mp (by decide +kernel))

def profile34_node74_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 7 82 44 104 17 49 64), lower := (rows 7 82 44 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 79 66 108 108 64 108 64) }] }

theorem profile34_node74 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,96] 6 17 profile34_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40,96] 6 17 profile34_node74_cert).mp (by decide +kernel))

def profile34_node68_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node68 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,40] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node68_route profile34_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node69
  · exact profile34_node70
  · exact profile34_node71
  · exact profile34_node72
  · exact profile34_node73
  · exact profile34_node74

def profile34_node75_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 7 82 52 105 121 105 64), lower := (rows 7 82 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 100 72 64 96 64) },{ target := 5, region := (rows 5 22 4 8 16 0 127), good := (rows 71 82 87 72 82 64 64) }] }

theorem profile34_node75 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,48] 6 105 profile34_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,48] 6 105 profile34_node75_cert).mp (by decide +kernel))

def profile34_node76_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 82 69 56 56 56 64), lower := (rows 7 82 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile34_node76 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,65] 6 56 profile34_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,65] 6 56 profile34_node76_cert).mp (by decide +kernel))

def profile34_node77_cert : CutBound 7 := { lost := (rows 0 32 48 0 0 0 0), upper := (rows 7 82 76 57 49 49 64), lower := (rows 7 82 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 71 66 76 76 64 96 64) },{ target := 5, region := (rows 1 18 12 8 16 0 127), good := (rows 71 82 76 76 82 64 64) }] }

theorem profile34_node77 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,72] 6 49 profile34_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,72] 6 49 profile34_node77_cert).mp (by decide +kernel))

def profile34_node78_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 7 82 84 41 57 41 64), lower := (rows 7 82 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 68 72 64 96 64) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile34_node78 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,80] 6 41 profile34_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,80] 6 41 profile34_node78_cert).mp (by decide +kernel))

def profile34_node79_cert : CutBound 7 := { lost := (rows 0 32 16 0 0 0 0), upper := (rows 7 82 100 57 57 57 64), lower := (rows 7 82 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 71 66 100 72 64 100 64) },{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 71 82 68 72 82 64 64) }] }

theorem profile34_node79 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,96] 6 57 profile34_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80,96] 6 57 profile34_node79_cert).mp (by decide +kernel))

def profile34_node57_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node57_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node57 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6,80] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile34_node57_route profile34_node57_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node58
  · exact profile34_node62
  · exact profile34_node63
  · exact profile34_node64
  · exact profile34_node68
  · exact profile34_node75
  · exact profile34_node76
  · exact profile34_node77
  · exact profile34_node78
  · exact profile34_node79

def profile34_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node1 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [6] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile34_node1_route profile34_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node2
  · exact profile34_node10
  · exact profile34_node23
  · exact profile34_node42
  · exact profile34_node55
  · exact profile34_node56
  · exact profile34_node57

def profile34_node82_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 19 7 28 104 112 96 64), lower := (rows 19 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 83 71 95 72 80 64 64) }] }

theorem profile34_node82 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,24] 6 96 profile34_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,24] 6 96 profile34_node82_cert).mp (by decide +kernel))

def profile34_node84_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 19 7 44 56 80 96 64), lower := (rows 19 7 44 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 99 103 108 108 96 96 96) },{ target := 5, region := (rows 7 6 4 8 127 0 127), good := (rows 83 87 95 88 80 80 80) }] }

theorem profile34_node84 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,48] 6 64 profile34_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,48] 6 64 profile34_node84_cert).mp (by decide +kernel))

def profile34_node85_cert : CutBound 7 := { lost := (rows 0 0 16 32 0 0 0), upper := (rows 19 7 44 88 112 96 64), lower := (rows 19 7 44 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 99 103 108 108 96 96 96) },{ target := 5, region := (rows 1 2 4 25 16 0 127), good := (rows 91 79 76 88 88 64 64) }] }

theorem profile34_node85 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,80] 6 96 profile34_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,80] 6 96 profile34_node85_cert).mp (by decide +kernel))

def profile34_node86_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 7 44 104 80 112 64), lower := (rows 19 7 44 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 67 79 108 108 64 108 64) }] }

theorem profile34_node86 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,96] 6 80 profile34_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40,96] 6 80 profile34_node86_cert).mp (by decide +kernel))

def profile34_node83_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node83_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node83 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,40] 6 (by decide) (choices 2) [48,80,96] profile34_node83_route profile34_node83_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node84
  · exact profile34_node85
  · exact profile34_node86

def profile34_node87_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 19 7 52 104 120 104 64), lower := (rows 19 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 83 71 87 72 80 64 64) }] }

theorem profile34_node87 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,48] 6 104 profile34_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,48] 6 104 profile34_node87_cert).mp (by decide +kernel))

def profile34_node88_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 7 76 120 112 112 64), lower := (rows 19 7 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 67 71 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 83 71 76 76 80 64 64) }] }

theorem profile34_node88 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,72] 6 112 profile34_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,72] 6 112 profile34_node88_cert).mp (by decide +kernel))

def profile34_node89_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 19 7 84 104 120 104 64), lower := (rows 19 7 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile34_node89 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,80] 6 104 profile34_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,80] 6 104 profile34_node89_cert).mp (by decide +kernel))

def profile34_node91_cert : Bound 7 := { allowed := (rows 96 112 0 64 0 0 0), upper := (rows 19 7 100 56 88 104 64), lower := (rows 19 7 100 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 8 0 40 127), good := (rows 67 71 100 108 64 100 64) }] }

theorem profile34_node91 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,48] 6 72 profile34_node91_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,48] 6 72 profile34_node91_cert).mp (by decide +kernel))

def profile34_node92_cert : Bound 7 := { allowed := (rows 96 112 0 32 0 0 0), upper := (rows 19 7 100 88 56 40 64), lower := (rows 19 7 100 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 8 0 40 127), good := (rows 67 71 100 108 64 100 64) }] }

theorem profile34_node92 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,80] 6 40 profile34_node92_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,80] 6 40 profile34_node92_cert).mp (by decide +kernel))

def profile34_node93_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 7 100 104 24 56 64), lower := (rows 19 7 100 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 67 79 108 108 64 108 64) }] }

theorem profile34_node93 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,96] 6 24 profile34_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96,96] 6 24 profile34_node93_cert).mp (by decide +kernel))

def profile34_node90_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node90_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node90 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5,96] 6 (by decide) (choices 2) [48,80,96] profile34_node90_route profile34_node90_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node91
  · exact profile34_node92
  · exact profile34_node93

def profile34_node81_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node81_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node81 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,5] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile34_node81_route profile34_node81_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node82
  · exact profile34_node83
  · exact profile34_node87
  · exact profile34_node88
  · exact profile34_node89
  · exact profile34_node90

def profile34_node95_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 14 21 104 112 96 64), lower := (rows 19 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 127 0 127 127), good := (rows 107 110 111 104 104 104 104) }] }

theorem profile34_node95 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,17] 6 96 profile34_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,17] 6 96 profile34_node95_cert).mp (by decide +kernel))

def profile34_node97_cert : CutBound 7 := { lost := (rows 32 0 16 0 0 0 0), upper := (rows 19 14 37 56 80 96 64), lower := (rows 19 14 37 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 103 110 101 104 96 96 96) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 95 85 88 80 80 80) }] }

theorem profile34_node97 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,48] 6 64 profile34_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,48] 6 64 profile34_node97_cert).mp (by decide +kernel))

def profile34_node98_cert : CutBound 7 := { lost := (rows 0 32 16 32 0 0 0), upper := (rows 19 14 37 88 112 96 64), lower := (rows 19 14 37 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 103 110 101 104 96 96 96) },{ target := 5, region := (rows 1 6 4 25 16 0 127), good := (rows 91 78 79 88 88 64 64) }] }

theorem profile34_node98 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,80] 6 96 profile34_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,80] 6 96 profile34_node98_cert).mp (by decide +kernel))

def profile34_node99_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 14 37 104 80 112 64), lower := (rows 19 14 37 104 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 44 0 32 127), good := (rows 67 78 111 104 64 104 64) }] }

theorem profile34_node99 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,96] 6 80 profile34_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33,96] 6 80 profile34_node99_cert).mp (by decide +kernel))

def profile34_node96_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node96_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node96 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,33] 6 (by decide) (choices 2) [48,80,96] profile34_node96_route profile34_node96_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node97
  · exact profile34_node98
  · exact profile34_node99

def profile34_node101_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 19 14 52 41 80 96 64), lower := (rows 19 14 52 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 107 110 100 105 96 96 96) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 95 84 89 80 80 80) }] }

theorem profile34_node101 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,33] 6 64 profile34_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,33] 6 64 profile34_node101_cert).mp (by decide +kernel))

def profile34_node102_cert : CutBound 7 := { lost := (rows 32 32 0 48 0 0 0), upper := (rows 19 14 52 73 112 96 64), lower := (rows 19 14 52 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 107 110 100 105 96 96 96) },{ target := 5, region := (rows 5 6 4 15 16 0 127), good := (rows 91 79 95 73 80 64 64) }] }

theorem profile34_node102 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,65] 6 96 profile34_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,65] 6 96 profile34_node102_cert).mp (by decide +kernel))

def profile34_node103_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 14 52 104 81 97 64), lower := (rows 19 14 52 104 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 45 0 33 127), good := (rows 107 78 110 104 64 104 64) }] }

theorem profile34_node103 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,96] 6 65 profile34_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48,96] 6 65 profile34_node103_cert).mp (by decide +kernel))

def profile34_node100_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node100_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node100 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,48] 6 (by decide) (choices 2) [33,65,96] profile34_node100_route profile34_node100_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node101
  · exact profile34_node102
  · exact profile34_node103

def profile34_node104_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 14 69 120 112 112 64), lower := (rows 19 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 78 69 72 64 96 64) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 87 78 69 72 80 64 64) }] }

theorem profile34_node104 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,65] 6 112 profile34_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,65] 6 112 profile34_node104_cert).mp (by decide +kernel))

def profile34_node105_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 19 14 84 105 113 97 64), lower := (rows 19 14 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 107 78 68 72 64 96 64) },{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 78 84 72 84 64 64) }] }

theorem profile34_node105 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,80] 6 97 profile34_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,80] 6 97 profile34_node105_cert).mp (by decide +kernel))

def profile34_node107_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 14 100 25 112 96 64), lower := (rows 19 14 100 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 127 8 0 127 127), good := (rows 103 110 100 111 100 100 100) }] }

theorem profile34_node107 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,17] 6 96 profile34_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,17] 6 96 profile34_node107_cert).mp (by decide +kernel))

def profile34_node108_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 14 100 41 80 112 64), lower := (rows 19 14 100 41 16 32 64), losses := [{ target := 4, region := (rows 1 10 44 8 0 32 127), good := (rows 67 78 100 111 64 100 64) }] }

theorem profile34_node108 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,33] 6 80 profile34_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,33] 6 80 profile34_node108_cert).mp (by decide +kernel))

def profile34_node109_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 14 100 56 81 97 64), lower := (rows 19 14 100 56 16 32 64), losses := [{ target := 4, region := (rows 1 10 45 8 0 33 127), good := (rows 103 78 100 110 64 100 64) }] }

theorem profile34_node109 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,48] 6 65 profile34_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,48] 6 65 profile34_node109_cert).mp (by decide +kernel))

def profile34_node110_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 14 100 73 48 48 64), lower := (rows 19 14 100 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 9 0 32 127), good := (rows 75 78 100 73 64 100 64) }] }

theorem profile34_node110 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,65] 6 48 profile34_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,65] 6 48 profile34_node110_cert).mp (by decide +kernel))

def profile34_node111_cert : Bound 7 := { allowed := (rows 96 112 0 32 0 0 0), upper := (rows 19 14 100 88 49 33 64), lower := (rows 19 14 100 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 37 8 0 33 127), good := (rows 103 78 100 72 64 100 64) }] }

theorem profile34_node111 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,80] 6 33 profile34_node111_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,80] 6 33 profile34_node111_cert).mp (by decide +kernel))

def profile34_node112_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 19 14 100 104 17 49 64), lower := (rows 19 14 100 104 16 32 64), losses := [{ target := 4, region := (rows 1 46 44 44 0 32 127), good := (rows 67 78 110 110 64 110 64) }] }

theorem profile34_node112 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,96] 6 17 profile34_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96,96] 6 17 profile34_node112_cert).mp (by decide +kernel))

def profile34_node106_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node106_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node106 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12,96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node106_route profile34_node106_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node107
  · exact profile34_node108
  · exact profile34_node109
  · exact profile34_node110
  · exact profile34_node111
  · exact profile34_node112

def profile34_node94_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile34_node94_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node94 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,12] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node94_route profile34_node94_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node95
  · exact profile34_node96
  · exact profile34_node100
  · exact profile34_node104
  · exact profile34_node105
  · exact profile34_node106

def profile34_node113_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 108 108 124 108 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 127 0 127 127), good := (rows 111 111 108 108 108 108 108) }] }

theorem profile34_node113 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,17] 6 108 profile34_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,17] 6 108 profile34_node113_cert).mp (by decide +kernel))

def profile34_node114_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 22 109 105 121 105 64), lower := (rows 19 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 70 68 72 64 96 64) }] }

theorem profile34_node114 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,20] 6 105 profile34_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,20] 6 105 profile34_node114_cert).mp (by decide +kernel))

def profile34_node117_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 28 44 80 96 64), lower := (rows 19 35 28 44 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 12 0 127 127), good := (rows 99 99 108 108 96 96 96) }] }

theorem profile34_node117 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,36] 6 64 profile34_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,36] 6 64 profile34_node117_cert).mp (by decide +kernel))

def profile34_node118_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 35 28 76 112 96 64), lower := (rows 19 35 28 76 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 12 0 127 127), good := (rows 99 99 108 108 96 96 96) }] }

theorem profile34_node118 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,68] 6 96 profile34_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,68] 6 96 profile34_node118_cert).mp (by decide +kernel))

def profile34_node119_cert : Bound 7 := { allowed := (rows 96 80 96 0 0 0 0), upper := (rows 19 35 28 104 84 100 64), lower := (rows 19 35 28 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 46 0 36 127), good := (rows 75 107 108 104 64 104 64) }] }

theorem profile34_node119 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,96] 6 68 profile34_node119_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24,96] 6 68 profile34_node119_cert).mp (by decide +kernel))

def profile34_node116_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node116_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node116 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,24] 6 (by decide) (choices 2) [36,68,96] profile34_node116_route profile34_node116_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node117
  · exact profile34_node118
  · exact profile34_node119

def profile34_node121_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 35 44 28 80 96 64), lower := (rows 19 35 44 28 16 32 64), losses := [{ target := 4, region := (rows 1 3 12 8 0 127 127), good := (rows 99 99 108 108 96 96 96) }] }

theorem profile34_node121 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,20] 6 64 profile34_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,20] 6 64 profile34_node121_cert).mp (by decide +kernel))

def profile34_node122_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 35 44 76 80 112 64), lower := (rows 19 35 44 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 38 47 0 32 127), good := (rows 79 111 108 76 64 108 64) }] }

theorem profile34_node122 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,68] 6 80 profile34_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,68] 6 80 profile34_node122_cert).mp (by decide +kernel))

def profile34_node123_cert : Bound 7 := { allowed := (rows 96 80 64 32 0 0 0), upper := (rows 19 35 44 88 84 100 64), lower := (rows 19 35 44 88 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 44 127), good := (rows 67 99 108 108 64 96 64) }] }

theorem profile34_node123 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,80] 6 68 profile34_node123_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40,80] 6 68 profile34_node123_cert).mp (by decide +kernel))

def profile34_node120_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile34_node120_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node120 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,40] 6 (by decide) (choices 2) [20,68,80] profile34_node120_route profile34_node120_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node121
  · exact profile34_node122
  · exact profile34_node123

def profile34_node124_cert : CutBound 7 := { lost := (rows 0 0 0 48 0 0 0), upper := (rows 19 35 52 76 92 108 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 67 99 108 72 64 96 64) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 83 67 92 72 80 64 64) }] }

theorem profile34_node124 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,48] 6 76 profile34_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,48] 6 76 profile34_node124_cert).mp (by decide +kernel))

def profile34_node125_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 35 76 124 116 116 64), lower := (rows 19 35 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 67 99 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 83 67 76 76 80 64 64) }] }

theorem profile34_node125 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,72] 6 116 profile34_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,72] 6 116 profile34_node125_cert).mp (by decide +kernel))

def profile34_node126_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 19 35 84 108 124 108 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 67 99 108 72 64 96 64) },{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile34_node126 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,80] 6 108 profile34_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,80] 6 108 profile34_node126_cert).mp (by decide +kernel))

def profile34_node127_cert : CutBound 7 := { lost := (rows 0 0 16 32 0 0 0), upper := (rows 19 35 100 92 92 124 64), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 83 67 92 72 80 64 64) }] }

theorem profile34_node127 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,96] 6 92 profile34_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33,96] 6 92 profile34_node127_cert).mp (by decide +kernel))

def profile34_node115_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node115_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node115 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,33] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile34_node115_route profile34_node115_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node116
  · exact profile34_node120
  · exact profile34_node124
  · exact profile34_node125
  · exact profile34_node126
  · exact profile34_node127

def profile34_node130_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 19 38 13 56 80 96 64), lower := (rows 19 38 13 56 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 111 104 96 96 96) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 87 93 88 80 80 80) }] }

theorem profile34_node130 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,48] 6 64 profile34_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,48] 6 64 profile34_node130_cert).mp (by decide +kernel))

def profile34_node131_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 19 38 13 88 112 96 64), lower := (rows 19 38 13 88 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 111 104 96 96 96) },{ target := 5, region := (rows 1 2 5 25 16 0 127), good := (rows 95 70 77 88 88 64 64) }] }

theorem profile34_node131 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,80] 6 96 profile34_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,80] 6 96 profile34_node131_cert).mp (by decide +kernel))


#print axioms profile34_node131
end Delivery.SmallBudgetTenFinite7
