import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile36_node2_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 19 19 117 121 113 113 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile36_node2 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,17] 6 113 profile36_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,17] 6 113 profile36_node2_cert).mp (by decide +kernel))

def profile36_node4_cert : CutBound 7 := { lost := (rows 0 0 32 1 0 0 0), upper := (rows 19 35 21 120 112 112 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 87 71 85 72 80 64 64) }] }

theorem profile36_node4 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,17] 6 112 profile36_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,17] 6 112 profile36_node4_cert).mp (by decide +kernel))

def profile36_node5_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 19 35 37 88 80 112 64), lower := (rows 19 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 71 103 103 72 64 96 64) }] }

theorem profile36_node5 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,33] 6 80 profile36_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,33] 6 80 profile36_node5_cert).mp (by decide +kernel))

def profile36_node6_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 19 35 52 89 81 113 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 91 84 72 80 64 64) }] }

theorem profile36_node6 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,48] 6 81 profile36_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,48] 6 81 profile36_node6_cert).mp (by decide +kernel))

def profile36_node7_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 19 35 69 120 112 112 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile36_node7 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,65] 6 112 profile36_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,65] 6 112 profile36_node7_cert).mp (by decide +kernel))

def profile36_node8_cert : CutBound 7 := { lost := (rows 0 0 33 0 0 0 0), upper := (rows 19 35 84 121 113 113 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile36_node8 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,80] 6 113 profile36_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,80] 6 113 profile36_node8_cert).mp (by decide +kernel))

def profile36_node9_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 19 35 100 89 81 113 64), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 86 102 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) }] }

theorem profile36_node9 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,96] 6 81 profile36_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33,96] 6 81 profile36_node9_cert).mp (by decide +kernel))

def profile36_node3_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node3 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,33] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node3_route profile36_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node4
  · exact profile36_node5
  · exact profile36_node6
  · exact profile36_node7
  · exact profile36_node8
  · exact profile36_node9

def profile36_node10_cert : CutBound 7 := { lost := (rows 96 0 0 0 0 0 0), upper := (rows 19 50 117 121 113 113 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 32 0), good := (rows 19 51 4 8 16 32 0) }] }

theorem profile36_node10 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,48] 6 113 profile36_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,48] 6 113 profile36_node10_cert).mp (by decide +kernel))

def profile36_node11_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 19 67 117 121 113 113 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile36_node11 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,65] 6 113 profile36_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,65] 6 113 profile36_node11_cert).mp (by decide +kernel))

def profile36_node12_cert : CutBound 7 := { lost := (rows 32 33 0 0 0 0 0), upper := (rows 19 82 117 121 113 113 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile36_node12 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,80] 6 113 profile36_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,80] 6 113 profile36_node12_cert).mp (by decide +kernel))

def profile36_node13_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 19 98 117 121 113 113 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile36_node13 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,96] 6 113 profile36_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18,96] 6 113 profile36_node13_cert).mp (by decide +kernel))

def profile36_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node1_route profile36_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node2
  · exact profile36_node3
  · exact profile36_node10
  · exact profile36_node11
  · exact profile36_node12
  · exact profile36_node13

def profile36_node16_cert : CutBound 7 := { lost := (rows 0 32 32 1 0 0 0), upper := (rows 35 19 21 120 112 112 64), lower := (rows 35 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 5, region := (rows 1 6 6 8 16 0 127), good := (rows 71 87 87 72 80 64 64) }] }

theorem profile36_node16 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,17] 6 112 profile36_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,17] 6 112 profile36_node16_cert).mp (by decide +kernel))

def profile36_node17_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 35 19 37 88 80 112 64), lower := (rows 35 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 71 101 72 64 96 64) }] }

theorem profile36_node17 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,33] 6 80 profile36_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,33] 6 80 profile36_node17_cert).mp (by decide +kernel))

def profile36_node18_cert : CutBound 7 := { lost := (rows 0 32 0 32 0 0 0), upper := (rows 35 19 52 89 81 113 64), lower := (rows 35 19 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 91 91 84 72 80 64 64) }] }

theorem profile36_node18 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,48] 6 81 profile36_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,48] 6 81 profile36_node18_cert).mp (by decide +kernel))

def profile36_node19_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 35 19 69 120 112 112 64), lower := (rows 35 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 103 71 69 72 64 96 64) }] }

theorem profile36_node19 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,65] 6 112 profile36_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,65] 6 112 profile36_node19_cert).mp (by decide +kernel))

def profile36_node20_cert : CutBound 7 := { lost := (rows 0 0 33 0 0 0 0), upper := (rows 35 19 84 121 113 113 64), lower := (rows 35 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 102 86 84 72 84 96 64) },{ target := 5, region := (rows 1 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile36_node20 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,80] 6 113 profile36_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,80] 6 113 profile36_node20_cert).mp (by decide +kernel))

def profile36_node21_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 35 19 100 89 81 113 64), lower := (rows 35 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 37 8 16 32 127), good := (rows 102 86 100 72 80 100 64) },{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 103 71 100 72 64 100 64) }] }

theorem profile36_node21 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,96] 6 81 profile36_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17,96] 6 81 profile36_node21_cert).mp (by decide +kernel))

def profile36_node15_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node15 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,17] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node15_route profile36_node15_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node16
  · exact profile36_node17
  · exact profile36_node18
  · exact profile36_node19
  · exact profile36_node20
  · exact profile36_node21

def profile36_node22_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 35 85 89 81 113 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile36_node22 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,33] 6 81 profile36_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,33] 6 81 profile36_node22_cert).mp (by decide +kernel))

def profile36_node23_cert : CutBound 7 := { lost := (rows 16 0 32 32 0 0 0), upper := (rows 35 50 85 89 81 113 64), lower := (rows 35 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 99 99 68 72 64 96 64) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile36_node23 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,48] 6 81 profile36_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,48] 6 81 profile36_node23_cert).mp (by decide +kernel))

def profile36_node24_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 67 117 121 113 113 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile36_node24 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,65] 6 113 profile36_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,65] 6 113 profile36_node24_cert).mp (by decide +kernel))

def profile36_node25_cert : CutBound 7 := { lost := (rows 0 33 0 0 0 0 0), upper := (rows 35 82 117 121 113 113 64), lower := (rows 35 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 98 82 68 72 82 96 64) },{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 67 82 68 72 82 64 64) }] }

theorem profile36_node25 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,80] 6 113 profile36_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,80] 6 113 profile36_node25_cert).mp (by decide +kernel))

def profile36_node26_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 35 98 85 89 81 113 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 35 4 8 16 32 127), good := (rows 98 98 68 72 80 98 64) },{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile36_node26 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,96] 6 81 profile36_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34,96] 6 81 profile36_node26_cert).mp (by decide +kernel))

def profile36_node14_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node14_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node14 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [34] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node14_route profile36_node14_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node15
  · exact profile36_node22
  · exact profile36_node23
  · exact profile36_node24
  · exact profile36_node25
  · exact profile36_node26

def profile36_node28_cert : CutBound 7 := { lost := (rows 0 96 0 0 0 0 0), upper := (rows 49 19 119 123 115 115 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) },{ target := 6, region := (rows 1 3 4 8 16 32 0), good := (rows 51 19 4 8 16 32 0) }] }

theorem profile36_node28 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,17] 6 115 profile36_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,17] 6 115 profile36_node28_cert).mp (by decide +kernel))

def profile36_node29_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 49 35 87 91 83 115 64), lower := (rows 49 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 99 68 72 64 96 64) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 81 95 68 72 80 64 64) }] }

theorem profile36_node29 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,33] 6 83 profile36_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,33] 6 83 profile36_node29_cert).mp (by decide +kernel))

def profile36_node30_cert : CutBound 7 := { lost := (rows 64 65 0 0 0 0 0), upper := (rows 49 50 87 91 83 115 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 114 114 68 72 80 96 64) },{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile36_node30 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,48] 6 83 profile36_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,48] 6 83 profile36_node30_cert).mp (by decide +kernel))

def profile36_node31_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 49 67 119 123 115 115 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile36_node31 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,65] 6 115 profile36_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,65] 6 115 profile36_node31_cert).mp (by decide +kernel))

def profile36_node32_cert : CutBound 7 := { lost := (rows 0 33 0 0 0 0 0), upper := (rows 49 82 119 123 115 115 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 68 72 82 96 64) },{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 68 72 82 64 64) }] }

theorem profile36_node32 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,80] 6 115 profile36_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,80] 6 115 profile36_node32_cert).mp (by decide +kernel))

def profile36_node33_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 49 98 87 91 83 115 64), lower := (rows 49 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 35 4 8 16 32 127), good := (rows 114 98 68 72 80 98 64) },{ target := 4, region := (rows 1 35 4 8 0 32 127), good := (rows 99 98 68 72 64 98 64) }] }

theorem profile36_node33 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,96] 6 83 profile36_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48,96] 6 83 profile36_node33_cert).mp (by decide +kernel))

def profile36_node27_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node27_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node27 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [48] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node27_route profile36_node27_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node28
  · exact profile36_node29
  · exact profile36_node30
  · exact profile36_node31
  · exact profile36_node32
  · exact profile36_node33

def profile36_node34_cert : CutBound 7 := { lost := (rows 48 0 0 0 0 0 0), upper := (rows 67 115 117 121 113 113 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) }] }

theorem profile36_node34 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [66] 6 113 profile36_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [66] 6 113 profile36_node34_cert).mp (by decide +kernel))

def profile36_node36_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 81 19 119 123 115 115 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile36_node36 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,17] 6 115 profile36_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,17] 6 115 profile36_node36_cert).mp (by decide +kernel))

def profile36_node38_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 81 35 7 120 112 112 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 122 126 120 120 120 120) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 71 72 64 96 64) }] }

theorem profile36_node38 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,3] 6 112 profile36_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,3] 6 112 profile36_node38_cert).mp (by decide +kernel))

def profile36_node39_cert : CutBound 7 := { lost := (rows 32 0 32 1 0 0 0), upper := (rows 81 35 21 122 114 114 64), lower := (rows 81 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 84 72 80 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile36_node39 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,17] 6 114 profile36_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,17] 6 114 profile36_node39_cert).mp (by decide +kernel))

def profile36_node41_cert : CutBound 7 := { lost := (rows 0 16 1 0 0 0 0), upper := (rows 81 35 22 25 112 96 64), lower := (rows 81 35 22 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 11 4 8 0 127 127), good := (rows 99 99 102 107 96 96 96) }] }

theorem profile36_node41 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,17] 6 96 profile36_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,17] 6 96 profile36_node41_cert).mp (by decide +kernel))

def profile36_node42_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 81 35 22 41 80 112 64), lower := (rows 81 35 22 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 10 4 10 0 32 127), good := (rows 65 107 78 107 64 96 64) }] }

theorem profile36_node42 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,33] 6 80 profile36_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,33] 6 80 profile36_node42_cert).mp (by decide +kernel))

def profile36_node43_cert : CutBound 7 := { lost := (rows 32 16 32 0 0 0 0), upper := (rows 81 35 22 56 81 97 64), lower := (rows 81 35 22 56 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 102 104 64 96 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile36_node43 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,48] 6 65 profile36_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,48] 6 65 profile36_node43_cert).mp (by decide +kernel))

def profile36_node44_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 81 35 22 73 48 48 64), lower := (rows 81 35 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 2 4 11 0 32 127), good := (rows 73 107 78 73 64 96 64) }] }

theorem profile36_node44 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,65] 6 48 profile36_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,65] 6 48 profile36_node44_cert).mp (by decide +kernel))

def profile36_node45_cert : CutBound 7 := { lost := (rows 0 16 0 1 0 0 0), upper := (rows 81 35 22 88 49 33 64), lower := (rows 81 35 22 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 29 16 32 127), good := (rows 88 106 94 88 88 96 64) },{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 102 72 64 96 64) }] }

theorem profile36_node45 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,80] 6 33 profile36_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,80] 6 33 profile36_node45_cert).mp (by decide +kernel))

def profile36_node46_cert : CutBound 7 := { lost := (rows 0 0 0 17 0 0 0), upper := (rows 81 35 22 104 17 49 64), lower := (rows 81 35 22 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 127), good := (rows 80 106 94 104 80 104 64) },{ target := 4, region := (rows 1 2 4 42 0 32 127), good := (rows 65 107 78 104 64 104 64) }] }

theorem profile36_node46 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,96] 6 17 profile36_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18,96] 6 17 profile36_node46_cert).mp (by decide +kernel))

def profile36_node40_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile36_node40_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node40 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,18] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node40_route profile36_node40_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node41
  · exact profile36_node42
  · exact profile36_node43
  · exact profile36_node44
  · exact profile36_node45
  · exact profile36_node46

def profile36_node47_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 81 35 37 90 82 114 64), lower := (rows 81 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 100 72 80 96 64) },{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 65 103 103 72 64 96 64) }] }

theorem profile36_node47 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,33] 6 82 profile36_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,33] 6 82 profile36_node47_cert).mp (by decide +kernel))

def profile36_node48_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 38 89 81 113 64), lower := (rows 81 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 102 72 64 96 64) }] }

theorem profile36_node48 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,34] 6 81 profile36_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,34] 6 81 profile36_node48_cert).mp (by decide +kernel))

def profile36_node49_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 35 52 91 83 115 64), lower := (rows 81 35 52 8 16 32 64), losses := [{ target := 5, region := (rows 23 2 4 10 18 0 127), good := (rows 81 91 85 72 81 64 64) }] }

theorem profile36_node49 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,48] 6 83 profile36_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,48] 6 83 profile36_node49_cert).mp (by decide +kernel))

def profile36_node50_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 81 35 69 58 50 50 64), lower := (rows 81 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 68 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 69 103 69 72 64 96 64) }] }

theorem profile36_node50 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,65] 6 50 profile36_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,65] 6 50 profile36_node50_cert).mp (by decide +kernel))

def profile36_node51_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 70 57 49 49 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 70 72 64 96 64) }] }

theorem profile36_node51 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,66] 6 49 profile36_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,66] 6 49 profile36_node51_cert).mp (by decide +kernel))

def profile36_node52_cert : CutBound 7 := { lost := (rows 32 0 33 0 0 0 0), upper := (rows 81 35 84 59 51 51 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile36_node52 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,80] 6 51 profile36_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,80] 6 51 profile36_node52_cert).mp (by decide +kernel))

def profile36_node53_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 35 100 27 19 51 64), lower := (rows 81 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 102 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 103 100 72 64 100 64) }] }

theorem profile36_node53 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,96] 6 19 profile36_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33,96] 6 19 profile36_node53_cert).mp (by decide +kernel))

def profile36_node37_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node37_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node37 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile36_node37_route profile36_node37_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node38
  · exact profile36_node39
  · exact profile36_node40
  · exact profile36_node47
  · exact profile36_node48
  · exact profile36_node49
  · exact profile36_node50
  · exact profile36_node51
  · exact profile36_node52
  · exact profile36_node53

def profile36_node55_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 81 50 7 121 113 113 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile36_node55 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,3] 6 113 profile36_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,3] 6 113 profile36_node55_cert).mp (by decide +kernel))

def profile36_node56_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 81 50 21 107 115 99 64), lower := (rows 81 50 21 8 16 32 64), losses := [{ target := 5, region := (rows 23 2 23 8 16 0 127), good := (rows 85 87 85 72 85 64 64) }] }

theorem profile36_node56 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,17] 6 99 profile36_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,17] 6 99 profile36_node56_cert).mp (by decide +kernel))

def profile36_node57_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 81 50 22 105 113 97 64), lower := (rows 81 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 86 72 80 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 98 70 72 64 96 64) }] }

theorem profile36_node57 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,18] 6 97 profile36_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,18] 6 97 profile36_node57_cert).mp (by decide +kernel))

def profile36_node58_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 50 37 91 83 115 64), lower := (rows 81 50 37 8 16 32 64), losses := [{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 91 69 72 81 64 64) }] }

theorem profile36_node58 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,33] 6 83 profile36_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,33] 6 83 profile36_node58_cert).mp (by decide +kernel))

def profile36_node59_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 50 38 89 81 113 64), lower := (rows 81 50 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 102 72 64 96 64) }] }

theorem profile36_node59 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,34] 6 81 profile36_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,34] 6 81 profile36_node59_cert).mp (by decide +kernel))

def profile36_node60_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 50 52 75 83 99 64), lower := (rows 81 50 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 127), good := (rows 80 118 118 72 80 96 64) }] }

theorem profile36_node60 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,48] 6 67 profile36_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,48] 6 67 profile36_node60_cert).mp (by decide +kernel))

def profile36_node61_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 50 69 59 51 51 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 98 69 72 64 96 64) },{ target := 5, region := (rows 19 2 23 8 16 0 127), good := (rows 85 87 69 72 85 64 64) }] }

theorem profile36_node61 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,65] 6 51 profile36_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,65] 6 51 profile36_node61_cert).mp (by decide +kernel))

def profile36_node62_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 50 70 57 49 49 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 70 72 64 96 64) }] }

theorem profile36_node62 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,66] 6 49 profile36_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,66] 6 49 profile36_node62_cert).mp (by decide +kernel))

def profile36_node63_cert : CutBound 7 := { lost := (rows 32 0 33 0 0 0 0), upper := (rows 81 50 84 43 51 35 64), lower := (rows 81 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 23 8 16 32 127), good := (rows 84 118 84 72 84 96 64) },{ target := 5, region := (rows 23 2 23 8 16 0 127), good := (rows 85 87 85 72 85 64 64) }] }

theorem profile36_node63 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,80] 6 35 profile36_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,80] 6 35 profile36_node63_cert).mp (by decide +kernel))

def profile36_node64_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 81 50 100 27 19 51 64), lower := (rows 81 50 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 118 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 102 100 72 64 100 64) }] }

theorem profile36_node64 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,96] 6 19 profile36_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48,96] 6 19 profile36_node64_cert).mp (by decide +kernel))

def profile36_node54_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node54_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node54 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,48] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile36_node54_route profile36_node54_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node55
  · exact profile36_node56
  · exact profile36_node57
  · exact profile36_node58
  · exact profile36_node59
  · exact profile36_node60
  · exact profile36_node61
  · exact profile36_node62
  · exact profile36_node63
  · exact profile36_node64

def profile36_node65_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 81 67 55 59 51 51 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile36_node65 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,65] 6 51 profile36_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,65] 6 51 profile36_node65_cert).mp (by decide +kernel))

def profile36_node66_cert : CutBound 7 := { lost := (rows 32 33 0 0 0 0 0), upper := (rows 81 82 55 59 51 51 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile36_node66 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,80] 6 51 profile36_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,80] 6 51 profile36_node66_cert).mp (by decide +kernel))

def profile36_node67_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 81 98 55 59 51 51 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 65 98 68 72 64 98 64) }] }

theorem profile36_node67 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,96] 6 51 profile36_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80,96] 6 51 profile36_node67_cert).mp (by decide +kernel))

def profile36_node35_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node35_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node35 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node35_route profile36_node35_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node36
  · exact profile36_node37
  · exact profile36_node54
  · exact profile36_node65
  · exact profile36_node66
  · exact profile36_node67

def profile36_node70_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 97 19 7 120 112 112 64), lower := (rows 97 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 122 126 120 120 120 120) },{ target := 4, region := (rows 33 2 6 8 0 32 127), good := (rows 97 71 71 72 64 97 64) }] }

theorem profile36_node70 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,3] 6 112 profile36_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,3] 6 112 profile36_node70_cert).mp (by decide +kernel))

def profile36_node71_cert : CutBound 7 := { lost := (rows 16 0 0 1 0 0 0), upper := (rows 97 19 21 122 114 114 64), lower := (rows 97 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 96 122 84 72 80 96 64) },{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 67 69 72 64 97 64) }] }

theorem profile36_node71 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,17] 6 114 profile36_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,17] 6 114 profile36_node71_cert).mp (by decide +kernel))

def profile36_node72_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 97 19 22 121 113 113 64), lower := (rows 97 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 96 86 86 72 80 96 64) },{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 67 70 72 64 97 64) }] }

theorem profile36_node72 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,18] 6 113 profile36_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,18] 6 113 profile36_node72_cert).mp (by decide +kernel))

def profile36_node73_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 97 19 37 90 82 114 64), lower := (rows 97 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 96 122 100 72 80 96 64) },{ target := 4, region := (rows 37 2 37 8 0 32 127), good := (rows 101 71 101 72 64 101 64) }] }

theorem profile36_node73 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,33] 6 82 profile36_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,33] 6 82 profile36_node73_cert).mp (by decide +kernel))

def profile36_node74_cert : CutBound 7 := { lost := (rows 16 32 0 32 0 0 0), upper := (rows 97 19 38 89 81 113 64), lower := (rows 97 19 38 8 16 32 64), losses := [{ target := 4, region := (rows 37 2 4 8 0 32 127), good := (rows 97 67 103 72 64 97 64) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 91 91 94 72 80 64 64) }] }

theorem profile36_node74 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,34] 6 81 profile36_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,34] 6 81 profile36_node74_cert).mp (by decide +kernel))

def profile36_node75_cert : CutBound 7 := { lost := (rows 16 32 0 32 0 0 0), upper := (rows 97 19 52 91 83 115 64), lower := (rows 97 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 37 2 4 8 0 32 127), good := (rows 97 67 101 72 64 97 64) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 91 91 84 72 80 64 64) }] }

theorem profile36_node75 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,48] 6 83 profile36_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,48] 6 83 profile36_node75_cert).mp (by decide +kernel))

def profile36_node76_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 97 19 69 58 50 50 64), lower := (rows 97 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 96 122 68 72 80 96 64) },{ target := 4, region := (rows 33 2 39 8 0 32 127), good := (rows 101 71 69 72 64 101 64) }] }

theorem profile36_node76 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,65] 6 50 profile36_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,65] 6 50 profile36_node76_cert).mp (by decide +kernel))

def profile36_node77_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 97 19 70 57 49 49 64), lower := (rows 97 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 96 86 70 72 80 96 64) },{ target := 4, region := (rows 33 2 6 8 0 32 127), good := (rows 97 71 70 72 64 97 64) }] }

theorem profile36_node77 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,66] 6 49 profile36_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,66] 6 49 profile36_node77_cert).mp (by decide +kernel))

def profile36_node78_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 97 19 84 59 51 51 64), lower := (rows 97 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 96 86 84 72 84 96 64) },{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 67 68 72 64 97 64) }] }

theorem profile36_node78 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,80] 6 51 profile36_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,80] 6 51 profile36_node78_cert).mp (by decide +kernel))

def profile36_node79_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 97 19 100 27 19 51 64), lower := (rows 97 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 37 8 16 32 127), good := (rows 100 86 100 72 80 100 64) },{ target := 4, region := (rows 37 2 37 8 0 32 127), good := (rows 101 71 101 72 64 101 64) }] }

theorem profile36_node79 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,96] 6 19 profile36_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17,96] 6 19 profile36_node79_cert).mp (by decide +kernel))

def profile36_node69_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node69_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node69 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile36_node69_route profile36_node69_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node70
  · exact profile36_node71
  · exact profile36_node72
  · exact profile36_node73
  · exact profile36_node74
  · exact profile36_node75
  · exact profile36_node76
  · exact profile36_node77
  · exact profile36_node78
  · exact profile36_node79

def profile36_node80_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 97 35 87 91 83 115 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile36_node80 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,33] 6 83 profile36_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,33] 6 83 profile36_node80_cert).mp (by decide +kernel))

def profile36_node82_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 97 50 7 89 81 113 64), lower := (rows 97 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 35 2 6 8 0 32 127), good := (rows 97 103 71 72 64 97 64) }] }

theorem profile36_node82 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,3] 6 81 profile36_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,3] 6 81 profile36_node82_cert).mp (by decide +kernel))

def profile36_node84_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 97 50 21 11 80 112 64), lower := (rows 97 50 21 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) },{ target := 4, region := (rows 35 2 4 10 0 32 127), good := (rows 97 107 69 75 64 97 64) }] }

theorem profile36_node84 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,3] 6 80 profile36_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,3] 6 80 profile36_node84_cert).mp (by decide +kernel))

def profile36_node85_cert : Bound 7 := { allowed := (rows 16 64 96 96 0 0 0), upper := (rows 97 50 21 25 82 98 64), lower := (rows 97 50 21 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) }] }

theorem profile36_node85 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,17] 6 66 profile36_node85_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,17] 6 66 profile36_node85_cert).mp (by decide +kernel))

def profile36_node86_cert : CutBound 7 := { lost := (rows 16 0 0 1 0 0 0), upper := (rows 97 50 21 26 81 97 64), lower := (rows 97 50 21 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 96 122 84 90 80 96 64) },{ target := 4, region := (rows 127 2 4 8 0 127 127), good := (rows 97 99 101 107 97 97 97) }] }

theorem profile36_node86 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,18] 6 65 profile36_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,18] 6 65 profile36_node86_cert).mp (by decide +kernel))

def profile36_node87_cert : Bound 7 := { allowed := (rows 16 64 96 48 0 0 0), upper := (rows 97 50 21 73 18 50 64), lower := (rows 97 50 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) }] }

theorem profile36_node87 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,65] 6 18 profile36_node87_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,65] 6 18 profile36_node87_cert).mp (by decide +kernel))

def profile36_node88_cert : CutBound 7 := { lost := (rows 16 0 0 17 0 0 0), upper := (rows 97 50 21 74 17 49 64), lower := (rows 97 50 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 96 122 84 74 80 96 64) },{ target := 4, region := (rows 35 2 4 10 0 32 127), good := (rows 97 107 69 75 64 97 64) }] }

theorem profile36_node88 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,66] 6 17 profile36_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,66] 6 17 profile36_node88_cert).mp (by decide +kernel))

def profile36_node89_cert : Bound 7 := { allowed := (rows 16 65 96 32 0 0 0), upper := (rows 97 50 21 88 19 35 64), lower := (rows 97 50 21 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 30 16 32 127), good := (rows 96 122 92 88 88 96 64) }] }

theorem profile36_node89 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,80] 6 3 profile36_node89_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17,80] 6 3 profile36_node89_cert).mp (by decide +kernel))

def profile36_node83_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile36_node83_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node83 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,17] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile36_node83_route profile36_node83_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node84
  · exact profile36_node85
  · exact profile36_node86
  · exact profile36_node87
  · exact profile36_node88
  · exact profile36_node89

def profile36_node90_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 97 50 22 89 81 113 64), lower := (rows 97 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 96 118 86 72 80 96 64) },{ target := 4, region := (rows 35 2 4 8 0 32 127), good := (rows 97 99 71 72 64 97 64) }] }

theorem profile36_node90 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,18] 6 81 profile36_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,18] 6 81 profile36_node90_cert).mp (by decide +kernel))

def profile36_node91_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 97 50 69 27 19 51 64), lower := (rows 97 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 35 2 39 8 0 32 127), good := (rows 101 103 69 72 64 101 64) }] }

theorem profile36_node91 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,65] 6 19 profile36_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,65] 6 19 profile36_node91_cert).mp (by decide +kernel))

def profile36_node92_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 97 50 70 25 17 49 64), lower := (rows 97 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 96 118 70 72 80 96 64) },{ target := 4, region := (rows 35 2 6 8 0 32 127), good := (rows 97 103 71 72 64 97 64) }] }

theorem profile36_node92 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,66] 6 17 profile36_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,66] 6 17 profile36_node92_cert).mp (by decide +kernel))

def profile36_node93_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 97 50 84 27 19 51 64), lower := (rows 97 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 96 118 84 72 84 96 64) },{ target := 4, region := (rows 35 2 4 8 0 32 127), good := (rows 97 99 68 72 64 97 64) }] }

theorem profile36_node93 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,80] 6 19 profile36_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48,80] 6 19 profile36_node93_cert).mp (by decide +kernel))

def profile36_node81_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile36_node81_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node81 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,48] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile36_node81_route profile36_node81_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node82
  · exact profile36_node83
  · exact profile36_node90
  · exact profile36_node91
  · exact profile36_node92
  · exact profile36_node93

def profile36_node94_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 97 67 55 59 51 51 64), lower := (rows 97 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile36_node94 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,65] 6 51 profile36_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,65] 6 51 profile36_node94_cert).mp (by decide +kernel))

def profile36_node95_cert : CutBound 7 := { lost := (rows 16 1 0 0 0 0 0), upper := (rows 97 82 55 59 51 51 64), lower := (rows 97 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 96 82 68 72 82 96 64) },{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 66 68 72 64 97 64) }] }

theorem profile36_node95 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,80] 6 51 profile36_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,80] 6 51 profile36_node95_cert).mp (by decide +kernel))

def profile36_node96_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 97 98 23 27 19 51 64), lower := (rows 97 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 35 4 8 16 32 127), good := (rows 98 98 68 72 80 98 64) },{ target := 4, region := (rows 35 35 4 8 0 32 127), good := (rows 99 99 68 72 64 99 64) }] }

theorem profile36_node96 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,96] 6 19 profile36_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96,96] 6 19 profile36_node96_cert).mp (by decide +kernel))

def profile36_node68_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node68 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile36_node68_route profile36_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node69
  · exact profile36_node80
  · exact profile36_node81
  · exact profile36_node94
  · exact profile36_node95
  · exact profile36_node96

def profile36_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile36_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile36_node0 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile36_node0_route profile36_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node1
  · exact profile36_node14
  · exact profile36_node27
  · exact profile36_node34
  · exact profile36_node35
  · exact profile36_node68

theorem profile36 : Upper (D (n:=7) [34,33,32,32,19,18,2]) (R (n:=7) [34,33,32,32,19,18,2]) [] 6 := profile36_node0


#print axioms profile36
end Delivery.SmallBudgetTenFinite7
