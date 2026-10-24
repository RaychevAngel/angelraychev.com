import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile37_node3_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 7 19 52 120 112 112 64), lower := (rows 7 19 52 8 16 32 64), losses := [{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 71 83 87 72 80 64 64) }] }

theorem profile37_node3 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,48] 6 112 profile37_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,48] 6 112 profile37_node3_cert).mp (by decide +kernel))

def profile37_node4_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 7 19 84 120 112 112 64), lower := (rows 7 19 84 8 16 32 64), losses := [{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile37_node4 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,80] 6 112 profile37_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,80] 6 112 profile37_node4_cert).mp (by decide +kernel))

def profile37_node5_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 7 19 100 120 112 112 64), lower := (rows 7 19 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 71 67 100 72 64 100 64) }] }

theorem profile37_node5 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,96] 6 112 profile37_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17,96] 6 112 profile37_node5_cert).mp (by decide +kernel))

def profile37_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node2 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,17] 6 (by decide) (choices 2) [48,80,96] profile37_node2_route profile37_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node3
  · exact profile37_node4
  · exact profile37_node5

def profile37_node7_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 35 52 88 80 112 64), lower := (rows 7 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 5 6 4 8 0 32 127), good := (rows 71 99 103 72 64 96 64) }] }

theorem profile37_node7 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,48] 6 80 profile37_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,48] 6 80 profile37_node7_cert).mp (by decide +kernel))

def profile37_node8_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 7 35 84 120 112 112 64), lower := (rows 7 35 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 127), good := (rows 71 67 84 72 84 64 64) }] }

theorem profile37_node8 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,80] 6 112 profile37_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,80] 6 112 profile37_node8_cert).mp (by decide +kernel))

def profile37_node9_cert : CutBound 7 := { lost := (rows 16 16 16 0 0 0 0), upper := (rows 7 35 100 88 80 112 64), lower := (rows 7 35 100 8 16 32 64), losses := [{ target := 4, region := (rows 39 38 38 8 0 32 127), good := (rows 71 103 103 72 64 103 64) }] }

theorem profile37_node9 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,96] 6 80 profile37_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33,96] 6 80 profile37_node9_cert).mp (by decide +kernel))

def profile37_node6_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node6 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,33] 6 (by decide) (choices 2) [48,80,96] profile37_node6_route profile37_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node7
  · exact profile37_node8
  · exact profile37_node9

def profile37_node11_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 7 50 21 120 112 112 64), lower := (rows 7 50 21 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 87 85 72 80 64 64) }] }

theorem profile37_node11 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,17] 6 112 profile37_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,17] 6 112 profile37_node11_cert).mp (by decide +kernel))

def profile37_node12_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 50 37 88 80 112 64), lower := (rows 7 50 37 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 6 8 0 32 127), good := (rows 71 103 101 72 64 96 64) }] }

theorem profile37_node12 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,33] 6 80 profile37_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,33] 6 80 profile37_node12_cert).mp (by decide +kernel))

def profile37_node13_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 7 50 52 89 81 113 64), lower := (rows 7 50 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 82 84 72 80 64 64) }] }

theorem profile37_node13 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,48] 6 81 profile37_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,48] 6 81 profile37_node13_cert).mp (by decide +kernel))

def profile37_node14_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 50 69 120 112 112 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile37_node14 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,65] 6 112 profile37_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,65] 6 112 profile37_node14_cert).mp (by decide +kernel))

def profile37_node15_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 7 50 84 121 113 113 64), lower := (rows 7 50 84 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile37_node15 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,80] 6 113 profile37_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,80] 6 113 profile37_node15_cert).mp (by decide +kernel))

def profile37_node16_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 50 100 89 81 113 64), lower := (rows 7 50 100 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) }] }

theorem profile37_node16 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,96] 6 81 profile37_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48,96] 6 81 profile37_node16_cert).mp (by decide +kernel))

def profile37_node10_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node10_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node10 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,48] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile37_node10_route profile37_node10_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node11
  · exact profile37_node12
  · exact profile37_node13
  · exact profile37_node14
  · exact profile37_node15
  · exact profile37_node16

def profile37_node17_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 67 116 120 112 112 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 127), good := (rows 71 67 71 72 64 96 64) }] }

theorem profile37_node17 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,65] 6 112 profile37_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,65] 6 112 profile37_node17_cert).mp (by decide +kernel))

def profile37_node18_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 7 82 117 121 113 113 64), lower := (rows 7 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 71 82 68 72 82 64 64) }] }

theorem profile37_node18 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,80] 6 113 profile37_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,80] 6 113 profile37_node18_cert).mp (by decide +kernel))

def profile37_node19_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 7 98 117 121 113 113 64), lower := (rows 7 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 71 98 68 72 64 98 64) }] }

theorem profile37_node19 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,96] 6 113 profile37_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6,96] 6 113 profile37_node19_cert).mp (by decide +kernel))

def profile37_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [6] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile37_node1_route profile37_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node2
  · exact profile37_node6
  · exact profile37_node10
  · exact profile37_node17
  · exact profile37_node18
  · exact profile37_node19

def profile37_node22_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 19 7 52 120 112 112 64), lower := (rows 19 7 52 8 16 32 64), losses := [{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 83 71 87 72 80 64 64) }] }

theorem profile37_node22 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,48] 6 112 profile37_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,48] 6 112 profile37_node22_cert).mp (by decide +kernel))

def profile37_node23_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 19 7 84 120 112 112 64), lower := (rows 19 7 84 8 16 32 64), losses := [{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile37_node23 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,80] 6 112 profile37_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,80] 6 112 profile37_node23_cert).mp (by decide +kernel))

def profile37_node24_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 19 7 100 120 112 112 64), lower := (rows 19 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 67 71 100 72 64 100 64) }] }

theorem profile37_node24 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,96] 6 112 profile37_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5,96] 6 112 profile37_node24_cert).mp (by decide +kernel))

def profile37_node21_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node21_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node21 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,5] 6 (by decide) (choices 2) [48,80,96] profile37_node21_route profile37_node21_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node22
  · exact profile37_node23
  · exact profile37_node24

def profile37_node25_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 19 19 116 124 116 116 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile37_node25 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,17] 6 116 profile37_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,17] 6 116 profile37_node25_cert).mp (by decide +kernel))

def profile37_node26_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 19 22 117 121 113 113 64), lower := (rows 19 22 4 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 87 68 72 80 64 64) }] }

theorem profile37_node26 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,20] 6 113 profile37_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,20] 6 113 profile37_node26_cert).mp (by decide +kernel))

def profile37_node28_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 19 35 52 92 84 116 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 83 67 92 72 80 64 64) }] }

theorem profile37_node28 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,48] 6 84 profile37_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,48] 6 84 profile37_node28_cert).mp (by decide +kernel))

def profile37_node29_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 19 35 84 124 116 116 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile37_node29 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,80] 6 116 profile37_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,80] 6 116 profile37_node29_cert).mp (by decide +kernel))

def profile37_node30_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 19 35 100 92 84 116 64), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) }] }

theorem profile37_node30 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,96] 6 84 profile37_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33,96] 6 84 profile37_node30_cert).mp (by decide +kernel))

def profile37_node27_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node27_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node27 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,33] 6 (by decide) (choices 2) [48,80,96] profile37_node27_route profile37_node27_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node28
  · exact profile37_node29
  · exact profile37_node30

def profile37_node32_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 19 38 21 120 112 112 64), lower := (rows 19 38 21 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 87 70 85 72 80 64 64) }] }

theorem profile37_node32 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,17] 6 112 profile37_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,17] 6 112 profile37_node32_cert).mp (by decide +kernel))

def profile37_node33_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 38 37 88 80 112 64), lower := (rows 19 38 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 102 103 72 64 96 64) }] }

theorem profile37_node33 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,33] 6 80 profile37_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,33] 6 80 profile37_node33_cert).mp (by decide +kernel))

def profile37_node34_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 38 52 89 81 113 64), lower := (rows 19 38 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 102 102 72 64 96 64) }] }

theorem profile37_node34 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,48] 6 81 profile37_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,48] 6 81 profile37_node34_cert).mp (by decide +kernel))

def profile37_node35_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 19 38 69 120 112 112 64), lower := (rows 19 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 102 69 72 64 96 64) }] }

theorem profile37_node35 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,65] 6 112 profile37_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,65] 6 112 profile37_node35_cert).mp (by decide +kernel))

def profile37_node36_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 19 38 84 121 113 113 64), lower := (rows 19 38 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 70 84 72 84 64 64) }] }

theorem profile37_node36 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,80] 6 113 profile37_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,80] 6 113 profile37_node36_cert).mp (by decide +kernel))

def profile37_node37_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 38 100 89 81 113 64), lower := (rows 19 38 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile37_node37 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,96] 6 81 profile37_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36,96] 6 81 profile37_node37_cert).mp (by decide +kernel))

def profile37_node31_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node31_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node31 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,36] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile37_node31_route profile37_node31_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node32
  · exact profile37_node33
  · exact profile37_node34
  · exact profile37_node35
  · exact profile37_node36
  · exact profile37_node37

def profile37_node38_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 19 50 117 125 117 117 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile37_node38 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,48] 6 117 profile37_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,48] 6 117 profile37_node38_cert).mp (by decide +kernel))

def profile37_node39_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 67 116 124 116 116 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile37_node39 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,65] 6 116 profile37_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,65] 6 116 profile37_node39_cert).mp (by decide +kernel))

def profile37_node40_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 70 117 121 113 113 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 70 70 72 64 96 64) }] }

theorem profile37_node40 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,68] 6 113 profile37_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,68] 6 113 profile37_node40_cert).mp (by decide +kernel))

def profile37_node41_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 19 82 117 125 117 117 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile37_node41 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,80] 6 117 profile37_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,80] 6 117 profile37_node41_cert).mp (by decide +kernel))

def profile37_node42_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 98 117 125 117 117 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile37_node42 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,96] 6 117 profile37_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18,96] 6 117 profile37_node42_cert).mp (by decide +kernel))

def profile37_node20_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node20 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile37_node20_route profile37_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node21
  · exact profile37_node25
  · exact profile37_node26
  · exact profile37_node27
  · exact profile37_node31
  · exact profile37_node38
  · exact profile37_node39
  · exact profile37_node40
  · exact profile37_node41
  · exact profile37_node42

def profile37_node45_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 7 52 88 80 112 64), lower := (rows 35 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 5 6 4 8 0 32 127), good := (rows 99 71 103 72 64 96 64) }] }

theorem profile37_node45 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,48] 6 80 profile37_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,48] 6 80 profile37_node45_cert).mp (by decide +kernel))

def profile37_node46_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 35 7 84 120 112 112 64), lower := (rows 35 7 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 127), good := (rows 67 71 84 72 84 64 64) }] }

theorem profile37_node46 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,80] 6 112 profile37_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,80] 6 112 profile37_node46_cert).mp (by decide +kernel))

def profile37_node47_cert : CutBound 7 := { lost := (rows 16 16 16 0 0 0 0), upper := (rows 35 7 100 88 80 112 64), lower := (rows 35 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 37 39 37 8 0 32 127), good := (rows 103 71 103 72 64 103 64) }] }

theorem profile37_node47 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,96] 6 80 profile37_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5,96] 6 80 profile37_node47_cert).mp (by decide +kernel))

def profile37_node44_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node44_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node44 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,5] 6 (by decide) (choices 2) [48,80,96] profile37_node44_route profile37_node44_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node45
  · exact profile37_node46
  · exact profile37_node47

def profile37_node49_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 35 19 52 92 84 116 64), lower := (rows 35 19 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 67 83 92 72 80 64 64) }] }

theorem profile37_node49 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,48] 6 84 profile37_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,48] 6 84 profile37_node49_cert).mp (by decide +kernel))

def profile37_node50_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 35 19 84 124 116 116 64), lower := (rows 35 19 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile37_node50 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,80] 6 116 profile37_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,80] 6 116 profile37_node50_cert).mp (by decide +kernel))

def profile37_node51_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 19 100 92 84 116 64), lower := (rows 35 19 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 103 71 100 72 64 100 64) }] }

theorem profile37_node51 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,96] 6 84 profile37_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17,96] 6 84 profile37_node51_cert).mp (by decide +kernel))

def profile37_node48_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node48_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node48 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,17] 6 (by decide) (choices 2) [48,80,96] profile37_node48_route profile37_node48_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node49
  · exact profile37_node50
  · exact profile37_node51

def profile37_node53_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 35 22 21 120 112 112 64), lower := (rows 35 22 21 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 86 87 72 80 64 64) }] }

theorem profile37_node53 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,17] 6 112 profile37_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,17] 6 112 profile37_node53_cert).mp (by decide +kernel))

def profile37_node54_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 22 37 88 80 112 64), lower := (rows 35 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 70 101 72 64 96 64) }] }

theorem profile37_node54 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,33] 6 80 profile37_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,33] 6 80 profile37_node54_cert).mp (by decide +kernel))

def profile37_node55_cert : CutBound 7 := { lost := (rows 0 32 0 32 0 0 0), upper := (rows 35 22 52 89 81 113 64), lower := (rows 35 22 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 9 17 0 127), good := (rows 91 86 86 72 80 64 64) }] }

theorem profile37_node55 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,48] 6 81 profile37_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,48] 6 81 profile37_node55_cert).mp (by decide +kernel))

def profile37_node56_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 22 69 120 112 112 64), lower := (rows 35 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 70 69 72 64 96 64) }] }

theorem profile37_node56 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,65] 6 112 profile37_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,65] 6 112 profile37_node56_cert).mp (by decide +kernel))

def profile37_node57_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 35 22 84 121 113 113 64), lower := (rows 35 22 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 22 22 8 16 0 127), good := (rows 71 86 86 72 86 64 64) }] }

theorem profile37_node57 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,80] 6 113 profile37_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,80] 6 113 profile37_node57_cert).mp (by decide +kernel))

def profile37_node58_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 22 100 89 81 113 64), lower := (rows 35 22 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 103 70 100 72 64 100 64) }] }

theorem profile37_node58 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,96] 6 81 profile37_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20,96] 6 81 profile37_node58_cert).mp (by decide +kernel))

def profile37_node52_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node52_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node52 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,20] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile37_node52_route profile37_node52_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node53
  · exact profile37_node54
  · exact profile37_node55
  · exact profile37_node56
  · exact profile37_node57
  · exact profile37_node58

def profile37_node59_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 35 84 92 84 116 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile37_node59 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,33] 6 84 profile37_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,33] 6 84 profile37_node59_cert).mp (by decide +kernel))

def profile37_node60_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 35 38 85 89 81 113 64), lower := (rows 35 38 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 99 103 68 72 64 96 64) }] }

theorem profile37_node60 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,36] 6 81 profile37_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,36] 6 81 profile37_node60_cert).mp (by decide +kernel))

def profile37_node61_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 35 50 85 93 85 117 64), lower := (rows 35 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 99 99 68 72 64 96 64) }] }

theorem profile37_node61 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,48] 6 85 profile37_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,48] 6 85 profile37_node61_cert).mp (by decide +kernel))

def profile37_node62_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 67 116 124 116 116 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile37_node62 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,65] 6 116 profile37_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,65] 6 116 profile37_node62_cert).mp (by decide +kernel))

def profile37_node63_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 35 70 117 121 113 113 64), lower := (rows 35 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 99 70 70 72 64 96 64) }] }

theorem profile37_node63 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,68] 6 113 profile37_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,68] 6 113 profile37_node63_cert).mp (by decide +kernel))

def profile37_node64_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 35 82 117 125 117 117 64), lower := (rows 35 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 67 82 68 72 82 64 64) }] }

theorem profile37_node64 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,80] 6 117 profile37_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,80] 6 117 profile37_node64_cert).mp (by decide +kernel))

def profile37_node65_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 98 85 93 85 117 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile37_node65 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,96] 6 85 profile37_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34,96] 6 85 profile37_node65_cert).mp (by decide +kernel))

def profile37_node43_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node43_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node43 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [34] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile37_node43_route profile37_node43_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node44
  · exact profile37_node48
  · exact profile37_node52
  · exact profile37_node59
  · exact profile37_node60
  · exact profile37_node61
  · exact profile37_node62
  · exact profile37_node63
  · exact profile37_node64
  · exact profile37_node65

def profile37_node68_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 49 7 22 120 112 112 64), lower := (rows 49 7 22 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile37_node68 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,18] 6 112 profile37_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,18] 6 112 profile37_node68_cert).mp (by decide +kernel))

def profile37_node69_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 7 38 88 80 112 64), lower := (rows 49 7 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 32 127), good := (rows 103 71 102 72 64 96 64) }] }

theorem profile37_node69 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,34] 6 80 profile37_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,34] 6 80 profile37_node69_cert).mp (by decide +kernel))

def profile37_node70_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 49 7 52 90 82 114 64), lower := (rows 49 7 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 81 95 84 72 80 64 64) }] }

theorem profile37_node70 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,48] 6 82 profile37_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,48] 6 82 profile37_node70_cert).mp (by decide +kernel))

def profile37_node71_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 7 70 120 112 112 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile37_node71 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,66] 6 112 profile37_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,66] 6 112 profile37_node71_cert).mp (by decide +kernel))

def profile37_node72_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 49 7 84 122 114 114 64), lower := (rows 49 7 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile37_node72 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,80] 6 114 profile37_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,80] 6 114 profile37_node72_cert).mp (by decide +kernel))

def profile37_node73_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 7 100 90 82 114 64), lower := (rows 49 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 37 8 0 32 127), good := (rows 103 71 100 72 64 100 64) }] }

theorem profile37_node73 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,96] 6 82 profile37_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5,96] 6 82 profile37_node73_cert).mp (by decide +kernel))

def profile37_node67_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node67_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node67 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,5] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile37_node67_route profile37_node67_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node68
  · exact profile37_node69
  · exact profile37_node70
  · exact profile37_node71
  · exact profile37_node72
  · exact profile37_node73

def profile37_node74_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 19 118 126 118 118 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile37_node74 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,17] 6 118 profile37_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,17] 6 118 profile37_node74_cert).mp (by decide +kernel))

def profile37_node76_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 49 22 7 120 112 112 64), lower := (rows 49 22 7 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 86 71 72 80 64 64) }] }

theorem profile37_node76 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,3] 6 112 profile37_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,3] 6 112 profile37_node76_cert).mp (by decide +kernel))

def profile37_node77_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 22 21 106 114 98 64), lower := (rows 49 22 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 110 69 72 64 96 64) }] }

theorem profile37_node77 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,17] 6 98 profile37_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,17] 6 98 profile37_node77_cert).mp (by decide +kernel))

def profile37_node78_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 22 22 105 113 97 64), lower := (rows 49 22 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 70 72 64 96 64) }] }

theorem profile37_node78 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,18] 6 97 profile37_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,18] 6 97 profile37_node78_cert).mp (by decide +kernel))

def profile37_node79_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 22 37 90 82 114 64), lower := (rows 49 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 101 72 64 96 64) }] }

theorem profile37_node79 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,33] 6 82 profile37_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,33] 6 82 profile37_node79_cert).mp (by decide +kernel))

def profile37_node80_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 49 22 38 89 81 113 64), lower := (rows 49 22 38 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 89 86 70 72 80 64 64) }] }

theorem profile37_node80 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,34] 6 81 profile37_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,34] 6 81 profile37_node80_cert).mp (by decide +kernel))

def profile37_node81_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 22 52 75 83 99 64), lower := (rows 49 22 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 81 86 86 72 80 64 64) }] }

theorem profile37_node81 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,48] 6 67 profile37_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,48] 6 67 profile37_node81_cert).mp (by decide +kernel))

def profile37_node82_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 22 69 122 114 114 64), lower := (rows 49 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 69 72 64 96 64) }] }

theorem profile37_node82 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,65] 6 114 profile37_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,65] 6 114 profile37_node82_cert).mp (by decide +kernel))

def profile37_node83_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 22 70 121 113 113 64), lower := (rows 49 22 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 97 70 70 72 64 96 64) }] }

theorem profile37_node83 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,66] 6 113 profile37_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,66] 6 113 profile37_node83_cert).mp (by decide +kernel))

def profile37_node84_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 49 22 84 107 115 99 64), lower := (rows 49 22 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 23 23 8 16 0 127), good := (rows 87 86 86 72 86 64 64) }] }

theorem profile37_node84 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,80] 6 99 profile37_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,80] 6 99 profile37_node84_cert).mp (by decide +kernel))

def profile37_node85_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 22 100 91 83 115 64), lower := (rows 49 22 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 101 70 100 72 64 100 64) }] }

theorem profile37_node85 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,96] 6 83 profile37_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20,96] 6 83 profile37_node85_cert).mp (by decide +kernel))

def profile37_node75_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node75_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node75 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,20] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile37_node75_route profile37_node75_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node76
  · exact profile37_node77
  · exact profile37_node78
  · exact profile37_node79
  · exact profile37_node80
  · exact profile37_node81
  · exact profile37_node82
  · exact profile37_node83
  · exact profile37_node84
  · exact profile37_node85

def profile37_node86_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 35 86 94 86 118 64), lower := (rows 49 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 99 68 72 64 96 64) }] }

theorem profile37_node86 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,33] 6 86 profile37_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,33] 6 86 profile37_node86_cert).mp (by decide +kernel))

def profile37_node88_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 38 7 88 80 112 64), lower := (rows 49 38 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 32 127), good := (rows 103 102 71 72 64 96 64) }] }

theorem profile37_node88 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,3] 6 80 profile37_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,3] 6 80 profile37_node88_cert).mp (by decide +kernel))

def profile37_node89_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 49 38 21 90 82 114 64), lower := (rows 49 38 21 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 10 18 0 127), good := (rows 85 94 85 72 80 64 64) }] }

theorem profile37_node89 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,17] 6 82 profile37_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,17] 6 82 profile37_node89_cert).mp (by decide +kernel))

def profile37_node90_cert : CutBound 7 := { lost := (rows 0 0 0 32 0 0 0), upper := (rows 49 38 22 89 81 113 64), lower := (rows 49 38 22 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 89 70 86 72 80 64 64) }] }

theorem profile37_node90 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,18] 6 81 profile37_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,18] 6 81 profile37_node90_cert).mp (by decide +kernel))

def profile37_node91_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 38 69 90 82 114 64), lower := (rows 49 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 32 127), good := (rows 103 102 71 72 64 96 64) }] }

theorem profile37_node91 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,65] 6 82 profile37_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,65] 6 82 profile37_node91_cert).mp (by decide +kernel))

def profile37_node92_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 38 70 89 81 113 64), lower := (rows 49 38 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 35 39 8 0 32 127), good := (rows 103 102 70 72 64 102 64) }] }

theorem profile37_node92 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,66] 6 81 profile37_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,66] 6 81 profile37_node92_cert).mp (by decide +kernel))

def profile37_node93_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 49 38 84 91 83 115 64), lower := (rows 49 38 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 85 70 84 72 84 64 64) }] }

theorem profile37_node93 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,80] 6 83 profile37_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36,80] 6 83 profile37_node93_cert).mp (by decide +kernel))

def profile37_node87_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile37_node87_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node87 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,36] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile37_node87_route profile37_node87_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node88
  · exact profile37_node89
  · exact profile37_node90
  · exact profile37_node91
  · exact profile37_node92
  · exact profile37_node93

def profile37_node94_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 49 50 87 95 87 119 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile37_node94 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,48] 6 87 profile37_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,48] 6 87 profile37_node94_cert).mp (by decide +kernel))

def profile37_node95_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 118 126 118 118 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) }] }

theorem profile37_node95 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,65] 6 118 profile37_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,65] 6 118 profile37_node95_cert).mp (by decide +kernel))

def profile37_node96_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 70 119 123 115 115 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 97 70 70 72 64 96 64) }] }

theorem profile37_node96 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,68] 6 115 profile37_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,68] 6 115 profile37_node96_cert).mp (by decide +kernel))

def profile37_node97_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 82 119 127 119 119 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 68 72 82 64 64) }] }

theorem profile37_node97 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,80] 6 119 profile37_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,80] 6 119 profile37_node97_cert).mp (by decide +kernel))

def profile37_node98_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 98 87 95 87 119 64), lower := (rows 49 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 35 4 8 0 32 127), good := (rows 99 98 68 72 64 98 64) }] }

theorem profile37_node98 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,96] 6 87 profile37_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48,96] 6 87 profile37_node98_cert).mp (by decide +kernel))

def profile37_node66_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node66_route : Route 7 := (fun mask => (mask,id))

theorem profile37_node66 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [48] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile37_node66_route profile37_node66_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node67
  · exact profile37_node74
  · exact profile37_node75
  · exact profile37_node86
  · exact profile37_node87
  · exact profile37_node94
  · exact profile37_node95
  · exact profile37_node96
  · exact profile37_node97
  · exact profile37_node98

def profile37_node99_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 67 119 117 125 117 117 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile37_node99 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [66] 6 117 profile37_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [66] 6 117 profile37_node99_cert).mp (by decide +kernel))

def profile37_node100_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 81 119 119 127 119 119 64), lower := (rows 81 2 4 8 16 32 64), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 66 68 72 81 64 64) }] }

theorem profile37_node100 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [80] 6 119 profile37_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [80] 6 119 profile37_node100_cert).mp (by decide +kernel))

def profile37_node101_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 97 119 119 127 119 119 64), lower := (rows 97 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 66 68 72 64 97 64) }] }

theorem profile37_node101 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [96] 6 119 profile37_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [96] 6 119 profile37_node101_cert).mp (by decide +kernel))

def profile37_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile37_node0_route : Route 7 := (fun mask => match mask with | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile37_node0 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [] 6 (by decide) (choices 2) [6,18,34,48,66,80,96] profile37_node0_route profile37_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile37_node1
  · exact profile37_node20
  · exact profile37_node43
  · exact profile37_node66
  · exact profile37_node99
  · exact profile37_node100
  · exact profile37_node101

theorem profile37 : Upper (D (n:=7) [33,33,33,32,19,18,2]) (R (n:=7) [33,33,33,32,19,18,2]) [] 6 := profile37_node0


#print axioms profile37
end Delivery.SmallBudgetTenFinite7
