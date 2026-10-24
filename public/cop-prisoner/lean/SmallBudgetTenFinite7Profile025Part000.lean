import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile25_node3_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 7 19 7 120 112 112 64), lower := (rows 7 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 125 120 120 120 120) }] }

theorem profile25_node3 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,3] 6 112 profile25_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,3] 6 112 profile25_node3_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 19 21 106 114 98 64), lower := (rows 7 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 126 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 69 85 85 72 80 96 64) }] }

theorem profile25_node4 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,17] 6 98 profile25_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,17] 6 98 profile25_node4_cert).mp (by decide +kernel))

def profile25_node5_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 7 19 22 105 113 97 64), lower := (rows 7 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 86 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 125 121 124 72 80 96 64) }] }

theorem profile25_node5 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,18] 6 97 profile25_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,18] 6 97 profile25_node5_cert).mp (by decide +kernel))

def profile25_node7_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 19 37 26 80 96 64), lower := (rows 7 19 37 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 127 127 127), good := (rows 126 122 124 122 112 112 112) },{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) }] }

theorem profile25_node7 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,18] 6 64 profile25_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,18] 6 64 profile25_node7_cert).mp (by decide +kernel))

def profile25_node8_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 19 37 74 80 112 64), lower := (rows 7 19 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 127 127 127), good := (rows 126 122 124 122 112 112 112) },{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) }] }

theorem profile25_node8 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,66] 6 80 profile25_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,66] 6 80 profile25_node8_cert).mp (by decide +kernel))

def profile25_node9_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 7 19 37 88 82 98 64), lower := (rows 7 19 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 31 19 35 127), good := (rows 126 122 124 88 88 96 64) },{ target := 1, region := (rows 1 0 4 26 16 32 127), good := (rows 77 89 101 88 88 96 64) }] }

theorem profile25_node9 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,80] 6 66 profile25_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33,80] 6 66 profile25_node9_cert).mp (by decide +kernel))

def profile25_node6_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node6 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,33] 6 (by decide) (choices 2) [18,66,80] profile25_node6_route profile25_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node7
  · exact profile25_node8
  · exact profile25_node9

def profile25_node10_cert : CutBound 7 := { lost := (rows 16 0 0 2 0 0 0), upper := (rows 7 19 38 89 81 113 64), lower := (rows 7 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 125 121 124 72 80 96 64) },{ target := 4, region := (rows 5 2 4 8 0 32 127), good := (rows 71 67 103 72 64 96 64) }] }

theorem profile25_node10 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,34] 6 81 profile25_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,34] 6 81 profile25_node10_cert).mp (by decide +kernel))

def profile25_node11_cert : CutBound 7 := { lost := (rows 64 64 0 16 0 0 0), upper := (rows 7 19 52 75 83 99 64), lower := (rows 7 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 111 107 100 72 64 96 64) },{ target := 6, region := (rows 5 6 4 8 16 32 0), good := (rows 7 19 55 8 16 32 0) }] }

theorem profile25_node11 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,48] 6 67 profile25_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,48] 6 67 profile25_node11_cert).mp (by decide +kernel))

def profile25_node12_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 19 69 122 114 114 64), lower := (rows 7 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 126 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 69 85 69 72 80 96 64) }] }

theorem profile25_node12 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,65] 6 114 profile25_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,65] 6 114 profile25_node12_cert).mp (by decide +kernel))

def profile25_node13_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 7 19 70 121 113 113 64), lower := (rows 7 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 86 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 125 121 124 72 80 96 64) }] }

theorem profile25_node13 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,66] 6 113 profile25_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,66] 6 113 profile25_node13_cert).mp (by decide +kernel))

def profile25_node14_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 7 19 84 107 115 99 64), lower := (rows 7 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 86 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 85 84 72 84 96 64) }] }

theorem profile25_node14 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,80] 6 99 profile25_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,80] 6 99 profile25_node14_cert).mp (by decide +kernel))

def profile25_node15_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 7 19 100 91 83 115 64), lower := (rows 7 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 70 82 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 69 81 100 72 80 100 64) }] }

theorem profile25_node15 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,96] 6 83 profile25_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17,96] 6 83 profile25_node15_cert).mp (by decide +kernel))

def profile25_node2_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node2 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node2_route profile25_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node3
  · exact profile25_node4
  · exact profile25_node5
  · exact profile25_node6
  · exact profile25_node10
  · exact profile25_node11
  · exact profile25_node12
  · exact profile25_node13
  · exact profile25_node14
  · exact profile25_node15

def profile25_node17_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 7 35 7 88 80 112 64), lower := (rows 7 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 125 120 120 120 120) }] }

theorem profile25_node17 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,3] 6 80 profile25_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,3] 6 80 profile25_node17_cert).mp (by decide +kernel))

def profile25_node19_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 35 21 26 80 96 64), lower := (rows 7 35 21 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 127 127 127), good := (rows 126 122 124 122 112 112 112) },{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) }] }

theorem profile25_node19 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,18] 6 64 profile25_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,18] 6 64 profile25_node19_cert).mp (by decide +kernel))

def profile25_node20_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 35 21 74 80 112 64), lower := (rows 7 35 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 127 127 127), good := (rows 126 122 124 122 112 112 112) },{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) }] }

theorem profile25_node20 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,66] 6 80 profile25_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,66] 6 80 profile25_node20_cert).mp (by decide +kernel))

def profile25_node21_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 7 35 21 88 82 98 64), lower := (rows 7 35 21 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 31 19 35 127), good := (rows 126 122 124 88 88 96 64) },{ target := 1, region := (rows 1 0 4 28 16 32 127), good := (rows 77 97 93 88 88 96 64) }] }

theorem profile25_node21 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,80] 6 66 profile25_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17,80] 6 66 profile25_node21_cert).mp (by decide +kernel))

def profile25_node18_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node18 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,17] 6 (by decide) (choices 2) [18,66,80] profile25_node18_route profile25_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node19
  · exact profile25_node20
  · exact profile25_node21

def profile25_node22_cert : CutBound 7 := { lost := (rows 16 0 0 2 0 0 0), upper := (rows 7 35 22 89 81 113 64), lower := (rows 7 35 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 125 121 124 72 80 96 64) },{ target := 4, region := (rows 5 2 4 8 0 32 127), good := (rows 71 99 71 72 64 96 64) }] }

theorem profile25_node22 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,18] 6 81 profile25_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,18] 6 81 profile25_node22_cert).mp (by decide +kernel))

def profile25_node23_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 7 35 69 90 82 114 64), lower := (rows 7 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 126 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 69 101 69 72 80 96 64) }] }

theorem profile25_node23 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,65] 6 82 profile25_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,65] 6 82 profile25_node23_cert).mp (by decide +kernel))

def profile25_node24_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 7 35 70 89 81 113 64), lower := (rows 7 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 102 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 125 121 124 72 80 96 64) }] }

theorem profile25_node24 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,66] 6 81 profile25_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,66] 6 81 profile25_node24_cert).mp (by decide +kernel))

def profile25_node25_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 7 35 84 91 83 115 64), lower := (rows 7 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 70 98 84 72 84 96 64) },{ target := 1, region := (rows 1 0 20 8 16 32 127), good := (rows 69 97 84 72 84 96 64) }] }

theorem profile25_node25 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,80] 6 83 profile25_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33,80] 6 83 profile25_node25_cert).mp (by decide +kernel))

def profile25_node16_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node16_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node16 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node16_route profile25_node16_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node17
  · exact profile25_node18
  · exact profile25_node22
  · exact profile25_node23
  · exact profile25_node24
  · exact profile25_node25

def profile25_node27_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 7 50 7 89 81 113 64), lower := (rows 7 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 125 112 125 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) }] }

theorem profile25_node27 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,3] 6 81 profile25_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,3] 6 81 profile25_node27_cert).mp (by decide +kernel))

def profile25_node28_cert : CutBound 7 := { lost := (rows 64 0 64 16 0 0 0), upper := (rows 7 50 21 75 83 99 64), lower := (rows 7 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 109 72 64 96 64) },{ target := 6, region := (rows 3 2 6 8 16 32 0), good := (rows 7 55 21 8 16 32 0) }] }

theorem profile25_node28 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,17] 6 67 profile25_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,17] 6 67 profile25_node28_cert).mp (by decide +kernel))

def profile25_node29_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 7 50 22 73 81 97 64), lower := (rows 7 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 118 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 125 112 84 72 80 96 64) }] }

theorem profile25_node29 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,18] 6 65 profile25_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,18] 6 65 profile25_node29_cert).mp (by decide +kernel))

def profile25_node30_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 7 50 69 91 83 115 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 112 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile25_node30 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,65] 6 83 profile25_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,65] 6 83 profile25_node30_cert).mp (by decide +kernel))

def profile25_node31_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 7 50 70 89 81 113 64), lower := (rows 7 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 118 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 125 112 68 72 80 96 64) }] }

theorem profile25_node31 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,66] 6 81 profile25_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,66] 6 81 profile25_node31_cert).mp (by decide +kernel))

def profile25_node32_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 7 50 84 75 83 99 64), lower := (rows 7 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 116 84 72 84 96 64) }] }

theorem profile25_node32 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,80] 6 67 profile25_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48,80] 6 67 profile25_node32_cert).mp (by decide +kernel))

def profile25_node26_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node26 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,48] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node26_route profile25_node26_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node27
  · exact profile25_node28
  · exact profile25_node29
  · exact profile25_node30
  · exact profile25_node31
  · exact profile25_node32

def profile25_node33_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 67 119 123 115 115 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 127), good := (rows 71 67 71 72 64 96 64) }] }

theorem profile25_node33 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,65] 6 115 profile25_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,65] 6 115 profile25_node33_cert).mp (by decide +kernel))

def profile25_node35_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 7 82 7 121 113 113 64), lower := (rows 7 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 70 72 82 96 64) },{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 125 80 125 72 80 96 64) }] }

theorem profile25_node35 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,3] 6 113 profile25_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,3] 6 113 profile25_node35_cert).mp (by decide +kernel))

def profile25_node36_cert : CutBound 7 := { lost := (rows 0 1 0 16 0 0 0), upper := (rows 7 82 21 107 115 99 64), lower := (rows 7 82 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 16 32 127), good := (rows 70 82 86 72 82 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 109 72 64 96 64) }] }

theorem profile25_node36 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,17] 6 99 profile25_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,17] 6 99 profile25_node36_cert).mp (by decide +kernel))

def profile25_node37_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 82 22 105 113 97 64), lower := (rows 7 82 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) }] }

theorem profile25_node37 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,18] 6 97 profile25_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,18] 6 97 profile25_node37_cert).mp (by decide +kernel))

def profile25_node39_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 7 82 37 11 80 112 64), lower := (rows 7 82 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 13 8 127 127 127), good := (rows 117 112 117 125 112 112 112) }] }

theorem profile25_node39 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,3] 6 80 profile25_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,3] 6 80 profile25_node39_cert).mp (by decide +kernel))

def profile25_node40_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 7 82 37 25 82 98 64), lower := (rows 7 82 37 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 3 2 15 8 0 35 127), good := (rows 103 103 101 109 64 96 64) }] }

theorem profile25_node40 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,17] 6 66 profile25_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,17] 6 66 profile25_node40_cert).mp (by decide +kernel))

def profile25_node41_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 82 37 26 81 97 64), lower := (rows 7 82 37 26 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 78 90 100 90 90 96 64) }] }

theorem profile25_node41 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,18] 6 65 profile25_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,18] 6 65 profile25_node41_cert).mp (by decide +kernel))

def profile25_node42_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 7 82 37 73 18 50 64), lower := (rows 7 82 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 77 80 109 73 80 96 64) }] }

theorem profile25_node42 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,65] 6 18 profile25_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,65] 6 18 profile25_node42_cert).mp (by decide +kernel))

def profile25_node43_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 82 37 74 17 49 64), lower := (rows 7 82 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 27 16 32 127), good := (rows 78 90 108 74 90 96 64) }] }

theorem profile25_node43 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,66] 6 17 profile25_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,66] 6 17 profile25_node43_cert).mp (by decide +kernel))

def profile25_node44_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 82 37 88 19 35 64), lower := (rows 7 82 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 78 90 100 90 90 96 64) }] }

theorem profile25_node44 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,80] 6 3 profile25_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33,80] 6 3 profile25_node44_cert).mp (by decide +kernel))

def profile25_node38_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node38_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node38 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node38_route profile25_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node39
  · exact profile25_node40
  · exact profile25_node41
  · exact profile25_node42
  · exact profile25_node43
  · exact profile25_node44

def profile25_node45_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 7 82 38 89 81 113 64), lower := (rows 7 82 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 102 72 82 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 125 80 100 72 80 96 64) }] }

theorem profile25_node45 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,34] 6 81 profile25_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,34] 6 81 profile25_node45_cert).mp (by decide +kernel))

def profile25_node46_cert : CutBound 7 := { lost := (rows 0 1 0 16 0 0 0), upper := (rows 7 82 52 75 83 99 64), lower := (rows 7 82 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 16 32 127), good := (rows 70 82 118 72 82 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 100 72 64 96 64) }] }

theorem profile25_node46 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,48] 6 67 profile25_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,48] 6 67 profile25_node46_cert).mp (by decide +kernel))

def profile25_node47_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 7 82 69 59 51 51 64), lower := (rows 7 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 68 72 82 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 80 69 72 80 96 64) }] }

theorem profile25_node47 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,65] 6 51 profile25_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,65] 6 51 profile25_node47_cert).mp (by decide +kernel))

def profile25_node48_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 82 70 57 49 49 64), lower := (rows 7 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 23 8 16 32 127), good := (rows 70 86 70 72 86 96 64) }] }

theorem profile25_node48 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,66] 6 49 profile25_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,66] 6 49 profile25_node48_cert).mp (by decide +kernel))

def profile25_node49_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 82 84 43 51 35 64), lower := (rows 7 82 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) }] }

theorem profile25_node49 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,80] 6 35 profile25_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,80] 6 35 profile25_node49_cert).mp (by decide +kernel))

def profile25_node50_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 82 100 27 19 51 64), lower := (rows 7 82 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 36 8 16 32 127), good := (rows 70 82 100 72 82 100 64) }] }

theorem profile25_node50 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,96] 6 19 profile25_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80,96] 6 19 profile25_node50_cert).mp (by decide +kernel))

def profile25_node34_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node34_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node34 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,80] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node34_route profile25_node34_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node35
  · exact profile25_node36
  · exact profile25_node37
  · exact profile25_node38
  · exact profile25_node45
  · exact profile25_node46
  · exact profile25_node47
  · exact profile25_node48
  · exact profile25_node49
  · exact profile25_node50

def profile25_node51_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 7 98 87 91 83 115 64), lower := (rows 7 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 70 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 71 98 68 72 64 98 64) }] }

theorem profile25_node51 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,96] 6 83 profile25_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6,96] 6 83 profile25_node51_cert).mp (by decide +kernel))

def profile25_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node1 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [6] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile25_node1_route profile25_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node2
  · exact profile25_node16
  · exact profile25_node26
  · exact profile25_node33
  · exact profile25_node34
  · exact profile25_node51

def profile25_node54_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 7 7 120 112 112 64), lower := (rows 19 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 125 120 120 120 120) }] }

theorem profile25_node54 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,3] 6 112 profile25_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,3] 6 112 profile25_node54_cert).mp (by decide +kernel))

def profile25_node55_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 19 7 21 106 114 98 64), lower := (rows 19 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 126 124 72 80 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 69 85 72 80 96 64) }] }

theorem profile25_node55 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,17] 6 98 profile25_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,17] 6 98 profile25_node55_cert).mp (by decide +kernel))

def profile25_node56_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 19 7 22 105 113 97 64), lower := (rows 19 7 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 70 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 125 124 72 80 96 64) }] }

theorem profile25_node56 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,18] 6 97 profile25_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,18] 6 97 profile25_node56_cert).mp (by decide +kernel))

def profile25_node57_cert : CutBound 7 := { lost := (rows 0 16 0 1 0 0 0), upper := (rows 19 7 37 90 82 114 64), lower := (rows 19 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 126 124 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 71 103 72 64 96 64) }] }

theorem profile25_node57 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,33] 6 82 profile25_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,33] 6 82 profile25_node57_cert).mp (by decide +kernel))

def profile25_node59_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 19 7 38 25 80 96 64), lower := (rows 19 7 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 1, region := (rows 1 0 4 11 127 127 127), good := (rows 121 125 124 121 112 112 112) }] }

theorem profile25_node59 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,17] 6 64 profile25_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,17] 6 64 profile25_node59_cert).mp (by decide +kernel))

def profile25_node60_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 19 7 38 73 80 112 64), lower := (rows 19 7 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 1, region := (rows 1 0 4 11 127 127 127), good := (rows 121 125 124 121 112 112 112) }] }

theorem profile25_node60 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,65] 6 80 profile25_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,65] 6 80 profile25_node60_cert).mp (by decide +kernel))

def profile25_node61_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 7 38 88 81 97 64), lower := (rows 19 7 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 78 102 88 88 96 64) },{ target := 1, region := (rows 1 0 4 31 19 35 127), good := (rows 121 125 124 88 88 96 64) }] }

theorem profile25_node61 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,80] 6 65 profile25_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34,80] 6 65 profile25_node61_cert).mp (by decide +kernel))

def profile25_node58_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node58_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node58 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,34] 6 (by decide) (choices 2) [17,65,80] profile25_node58_route profile25_node58_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node59
  · exact profile25_node60
  · exact profile25_node61

def profile25_node62_cert : CutBound 7 := { lost := (rows 64 64 0 16 0 0 0), upper := (rows 19 7 52 75 83 99 64), lower := (rows 19 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 107 111 100 72 64 96 64) },{ target := 6, region := (rows 5 6 4 8 16 32 0), good := (rows 19 7 55 8 16 32 0) }] }

theorem profile25_node62 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,48] 6 67 profile25_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,48] 6 67 profile25_node62_cert).mp (by decide +kernel))

def profile25_node63_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 19 7 69 122 114 114 64), lower := (rows 19 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 126 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 69 69 72 80 96 64) }] }

theorem profile25_node63 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,65] 6 114 profile25_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,65] 6 114 profile25_node63_cert).mp (by decide +kernel))

def profile25_node64_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 19 7 70 121 113 113 64), lower := (rows 19 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 70 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 125 124 72 80 96 64) }] }

theorem profile25_node64 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,66] 6 113 profile25_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,66] 6 113 profile25_node64_cert).mp (by decide +kernel))

def profile25_node65_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 7 84 107 115 99 64), lower := (rows 19 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 69 84 72 84 96 64) }] }

theorem profile25_node65 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,80] 6 99 profile25_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,80] 6 99 profile25_node65_cert).mp (by decide +kernel))

def profile25_node66_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 7 100 91 83 115 64), lower := (rows 19 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 70 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 81 69 100 72 80 100 64) }] }

theorem profile25_node66 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,96] 6 83 profile25_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5,96] 6 83 profile25_node66_cert).mp (by decide +kernel))

def profile25_node53_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node53_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node53 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,5] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node53_route profile25_node53_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node54
  · exact profile25_node55
  · exact profile25_node56
  · exact profile25_node57
  · exact profile25_node58
  · exact profile25_node62
  · exact profile25_node63
  · exact profile25_node64
  · exact profile25_node65
  · exact profile25_node66

def profile25_node67_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 103 111 119 103 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) }] }

theorem profile25_node67 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,17] 6 103 profile25_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,17] 6 103 profile25_node67_cert).mp (by decide +kernel))

def profile25_node68_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 22 103 107 115 99 64), lower := (rows 19 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 70 68 72 64 96 64) }] }

theorem profile25_node68 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,20] 6 99 profile25_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,20] 6 99 profile25_node68_cert).mp (by decide +kernel))

def profile25_node70_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 35 7 92 84 116 64), lower := (rows 19 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 126 72 80 96 64) },{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 81 97 125 72 80 96 64) }] }

theorem profile25_node70 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,3] 6 84 profile25_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,3] 6 84 profile25_node70_cert).mp (by decide +kernel))

def profile25_node71_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 19 35 21 78 86 102 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 101 85 72 80 96 64) },{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 67 99 111 72 64 96 64) }] }

theorem profile25_node71 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,17] 6 70 profile25_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,17] 6 70 profile25_node71_cert).mp (by decide +kernel))

def profile25_node72_cert : CutBound 7 := { lost := (rows 64 0 65 0 0 0 0), upper := (rows 19 35 22 77 85 101 64), lower := (rows 19 35 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 102 86 72 80 96 64) },{ target := 6, region := (rows 5 2 5 8 16 32 0), good := (rows 23 39 23 8 16 32 0) }] }

theorem profile25_node72 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,18] 6 69 profile25_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,18] 6 69 profile25_node72_cert).mp (by decide +kernel))

def profile25_node73_cert : CutBound 7 := { lost := (rows 0 0 18 0 0 0 0), upper := (rows 19 35 69 94 86 118 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 101 69 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile25_node73 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,65] 6 86 profile25_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,65] 6 86 profile25_node73_cert).mp (by decide +kernel))

def profile25_node74_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 19 35 70 93 85 117 64), lower := (rows 19 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 102 70 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 70 72 64 96 64) }] }

theorem profile25_node74 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,66] 6 85 profile25_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,66] 6 85 profile25_node74_cert).mp (by decide +kernel))

def profile25_node75_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 35 84 79 87 103 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 101 84 72 84 96 64) }] }

theorem profile25_node75 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,80] 6 71 profile25_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33,80] 6 71 profile25_node75_cert).mp (by decide +kernel))

def profile25_node69_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node69_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node69 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node69_route profile25_node69_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node70
  · exact profile25_node71
  · exact profile25_node72
  · exact profile25_node73
  · exact profile25_node74
  · exact profile25_node75

def profile25_node77_cert : CutBound 7 := { lost := (rows 0 0 16 2 0 0 0), upper := (rows 19 38 7 89 81 113 64), lower := (rows 19 38 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 124 125 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 102 71 72 64 96 64) }] }

theorem profile25_node77 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,3] 6 81 profile25_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,3] 6 81 profile25_node77_cert).mp (by decide +kernel))

def profile25_node78_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 19 38 21 75 83 99 64), lower := (rows 19 38 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 100 85 72 80 96 64) },{ target := 4, region := (rows 1 6 4 13 0 37 127), good := (rows 107 110 111 72 64 96 64) }] }

theorem profile25_node78 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,17] 6 67 profile25_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,17] 6 67 profile25_node78_cert).mp (by decide +kernel))

def profile25_node79_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 19 38 22 73 81 97 64), lower := (rows 19 38 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 102 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 100 84 72 80 96 64) }] }

theorem profile25_node79 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,18] 6 65 profile25_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,18] 6 65 profile25_node79_cert).mp (by decide +kernel))

def profile25_node80_cert : CutBound 7 := { lost := (rows 0 0 18 0 0 0 0), upper := (rows 19 38 69 91 83 115 64), lower := (rows 19 38 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 100 69 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 102 69 72 64 96 64) }] }

theorem profile25_node80 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,65] 6 83 profile25_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,65] 6 83 profile25_node80_cert).mp (by decide +kernel))

def profile25_node81_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 19 38 70 89 81 113 64), lower := (rows 19 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 39 8 16 32 127), good := (rows 86 102 70 72 80 102 64) }] }

theorem profile25_node81 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,66] 6 81 profile25_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,66] 6 81 profile25_node81_cert).mp (by decide +kernel))

def profile25_node82_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 38 84 75 83 99 64), lower := (rows 19 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 100 84 72 84 96 64) }] }

theorem profile25_node82 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,80] 6 67 profile25_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36,80] 6 67 profile25_node82_cert).mp (by decide +kernel))

def profile25_node76_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node76_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node76 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,36] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node76_route profile25_node76_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node77
  · exact profile25_node78
  · exact profile25_node79
  · exact profile25_node80
  · exact profile25_node81
  · exact profile25_node82

def profile25_node83_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 71 79 87 103 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) }] }

theorem profile25_node83 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,48] 6 71 profile25_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,48] 6 71 profile25_node83_cert).mp (by decide +kernel))

def profile25_node85_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 67 7 124 116 116 64), lower := (rows 19 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 66 126 72 80 96 64) },{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 81 65 125 72 80 96 64) }] }

theorem profile25_node85 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,3] 6 116 profile25_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,3] 6 116 profile25_node85_cert).mp (by decide +kernel))

def profile25_node86_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 19 67 21 110 118 102 64), lower := (rows 19 67 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 69 85 72 80 96 64) },{ target := 4, region := (rows 1 7 4 12 0 36 127), good := (rows 67 67 111 72 64 96 64) }] }

theorem profile25_node86 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,17] 6 102 profile25_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,17] 6 102 profile25_node86_cert).mp (by decide +kernel))

def profile25_node87_cert : CutBound 7 := { lost := (rows 0 16 1 0 0 0 0), upper := (rows 19 67 22 109 117 101 64), lower := (rows 19 67 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 70 86 72 80 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 70 72 64 96 64) }] }

theorem profile25_node87 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,18] 6 101 profile25_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,18] 6 101 profile25_node87_cert).mp (by decide +kernel))

def profile25_node89_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 19 67 37 14 80 112 64), lower := (rows 19 67 37 14 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) },{ target := 4, region := (rows 1 7 4 12 0 32 127), good := (rows 67 67 111 78 64 96 64) }] }

theorem profile25_node89 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,6] 6 80 profile25_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,6] 6 80 profile25_node89_cert).mp (by decide +kernel))

def profile25_node90_cert : Bound 7 := { allowed := (rows 64 16 82 64 0 0 0), upper := (rows 19 67 37 26 84 100 64), lower := (rows 19 67 37 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 9 20 36 127), good := (rows 90 74 124 90 80 96 64) }] }

theorem profile25_node90 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,18] 6 68 profile25_node90_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,18] 6 68 profile25_node90_cert).mp (by decide +kernel))

def profile25_node91_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 19 67 37 28 82 98 64), lower := (rows 19 67 37 28 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 35 127), good := (rows 114 114 124 92 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 47 127), good := (rows 103 103 103 110 64 96 64) }] }

theorem profile25_node91 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,20] 6 66 profile25_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,20] 6 66 profile25_node91_cert).mp (by decide +kernel))

def profile25_node92_cert : Bound 7 := { allowed := (rows 64 16 82 16 0 0 0), upper := (rows 19 67 37 74 20 52 64), lower := (rows 19 67 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 20 36 127), good := (rows 90 74 124 74 80 96 64) }] }

theorem profile25_node92 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,66] 6 20 profile25_node92_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,66] 6 20 profile25_node92_cert).mp (by decide +kernel))

def profile25_node93_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 67 37 76 18 50 64), lower := (rows 19 67 37 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 35 127), good := (rows 114 114 124 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 81 65 109 76 80 96 64) }] }

theorem profile25_node93 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,68] 6 18 profile25_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,68] 6 18 profile25_node93_cert).mp (by decide +kernel))

def profile25_node94_cert : Bound 7 := { allowed := (rows 64 16 82 2 0 0 0), upper := (rows 19 67 37 88 22 38 64), lower := (rows 19 67 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 74 108 88 88 96 64) }] }

theorem profile25_node94 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,80] 6 6 profile25_node94_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33,80] 6 6 profile25_node94_cert).mp (by decide +kernel))

def profile25_node88_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node88_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node88 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,33] 6 (by decide) (choices 2) [6,18,20,66,68,80] profile25_node88_route profile25_node88_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node89
  · exact profile25_node90
  · exact profile25_node91
  · exact profile25_node92
  · exact profile25_node93
  · exact profile25_node94

def profile25_node96_cert : CutBound 7 := { lost := (rows 0 16 1 0 0 0 0), upper := (rows 19 67 38 13 80 112 64), lower := (rows 19 67 38 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 4, region := (rows 1 11 4 8 0 32 127), good := (rows 67 67 102 79 64 96 64) }] }

theorem profile25_node96 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,5] 6 80 profile25_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,5] 6 80 profile25_node96_cert).mp (by decide +kernel))

def profile25_node97_cert : Bound 7 := { allowed := (rows 64 16 80 66 0 0 0), upper := (rows 19 67 38 25 84 100 64), lower := (rows 19 67 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 31 47 127), good := (rows 118 118 118 124 80 96 64) }] }

theorem profile25_node97 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,17] 6 68 profile25_node97_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,17] 6 68 profile25_node97_cert).mp (by decide +kernel))

def profile25_node98_cert : CutBound 7 := { lost := (rows 0 16 16 2 0 0 0), upper := (rows 19 67 38 28 81 97 64), lower := (rows 19 67 38 28 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 19 35 127), good := (rows 113 113 124 92 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 35 127), good := (rows 103 103 102 76 64 96 64) }] }

theorem profile25_node98 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,20] 6 65 profile25_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,20] 6 65 profile25_node98_cert).mp (by decide +kernel))

def profile25_node99_cert : Bound 7 := { allowed := (rows 64 16 80 18 0 0 0), upper := (rows 19 67 38 73 20 52 64), lower := (rows 19 67 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 31 47 127), good := (rows 118 118 118 124 80 96 64) }] }

theorem profile25_node99 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,65] 6 20 profile25_node99_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,65] 6 20 profile25_node99_cert).mp (by decide +kernel))

def profile25_node100_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 67 38 76 17 49 64), lower := (rows 19 67 38 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 82 66 110 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 19 35 127), good := (rows 113 113 124 76 80 96 64) }] }

theorem profile25_node100 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,68] 6 17 profile25_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,68] 6 17 profile25_node100_cert).mp (by decide +kernel))

def profile25_node101_cert : Bound 7 := { allowed := (rows 64 16 81 2 0 0 0), upper := (rows 19 67 38 88 21 37 64), lower := (rows 19 67 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 74 102 88 88 96 64) }] }

theorem profile25_node101 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,80] 6 5 profile25_node101_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34,80] 6 5 profile25_node101_cert).mp (by decide +kernel))

def profile25_node95_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node95_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node95 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,34] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile25_node95_route profile25_node95_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node96
  · exact profile25_node97
  · exact profile25_node98
  · exact profile25_node99
  · exact profile25_node100
  · exact profile25_node101

def profile25_node103_cert : Bound 7 := { allowed := (rows 64 16 66 80 0 0 0), upper := (rows 19 67 52 11 84 100 64), lower := (rows 19 67 52 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 126 116 116 116) }] }

theorem profile25_node103 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,3] 6 68 profile25_node103_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,3] 6 68 profile25_node103_cert).mp (by decide +kernel))

def profile25_node104_cert : CutBound 7 := { lost := (rows 0 16 1 0 0 0 0), upper := (rows 19 67 52 13 82 98 64), lower := (rows 19 67 52 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 19 35 127), good := (rows 118 118 116 124 80 96 64) },{ target := 4, region := (rows 1 11 4 8 0 43 127), good := (rows 99 99 100 111 64 96 64) }] }

theorem profile25_node104 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,5] 6 66 profile25_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,5] 6 66 profile25_node104_cert).mp (by decide +kernel))

def profile25_node105_cert : CutBound 7 := { lost := (rows 0 16 2 0 0 0 0), upper := (rows 19 67 52 14 81 97 64), lower := (rows 19 67 52 14 16 32 64), losses := [{ target := 1, region := (rows 1 0 15 8 19 35 127), good := (rows 117 117 116 124 80 96 64) },{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 100 110 64 96 64) }] }

theorem profile25_node105 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,6] 6 65 profile25_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,6] 6 65 profile25_node105_cert).mp (by decide +kernel))

def profile25_node106_cert : Bound 7 := { allowed := (rows 64 16 66 18 0 0 0), upper := (rows 19 67 52 73 22 38 64), lower := (rows 19 67 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 19 35 127), good := (rows 118 118 116 124 80 96 64) }] }

theorem profile25_node106 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,65] 6 6 profile25_node106_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,65] 6 6 profile25_node106_cert).mp (by decide +kernel))

def profile25_node107_cert : Bound 7 := { allowed := (rows 64 16 67 16 0 0 0), upper := (rows 19 67 52 74 21 37 64), lower := (rows 19 67 52 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 16 32 127), good := (rows 90 74 116 74 80 96 64) }] }

theorem profile25_node107 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,66] 6 5 profile25_node107_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,66] 6 5 profile25_node107_cert).mp (by decide +kernel))

def profile25_node108_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 19 67 52 76 19 35 64), lower := (rows 19 67 52 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 82 66 124 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 81 65 124 76 80 96 64) }] }

theorem profile25_node108 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,68] 6 3 profile25_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48,68] 6 3 profile25_node108_cert).mp (by decide +kernel))

def profile25_node102_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node102_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node102 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,48] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node102_route profile25_node102_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node103
  · exact profile25_node104
  · exact profile25_node105
  · exact profile25_node106
  · exact profile25_node107
  · exact profile25_node108

def profile25_node109_cert : CutBound 7 := { lost := (rows 0 16 18 0 0 0 0), upper := (rows 19 67 69 62 54 54 64), lower := (rows 19 67 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 69 69 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile25_node109 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,65] 6 54 profile25_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,65] 6 54 profile25_node109_cert).mp (by decide +kernel))

def profile25_node110_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 19 67 70 61 53 53 64), lower := (rows 19 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 71 71 70 72 64 96 64) }] }

theorem profile25_node110 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,66] 6 53 profile25_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,66] 6 53 profile25_node110_cert).mp (by decide +kernel))

def profile25_node111_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 67 84 47 55 39 64), lower := (rows 19 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 69 84 72 84 96 64) }] }

theorem profile25_node111 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,80] 6 39 profile25_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,80] 6 39 profile25_node111_cert).mp (by decide +kernel))

def profile25_node112_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 19 67 100 31 23 55 64), lower := (rows 19 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 66 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 81 65 100 72 80 100 64) }] }

theorem profile25_node112 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,96] 6 23 profile25_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65,96] 6 23 profile25_node112_cert).mp (by decide +kernel))

def profile25_node84_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node84_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node84 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,65] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node84_route profile25_node84_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node85
  · exact profile25_node86
  · exact profile25_node87
  · exact profile25_node88
  · exact profile25_node95
  · exact profile25_node102
  · exact profile25_node109
  · exact profile25_node110
  · exact profile25_node111
  · exact profile25_node112

def profile25_node113_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 19 70 119 123 115 115 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 70 70 72 64 96 64) }] }

theorem profile25_node113 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,68] 6 115 profile25_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,68] 6 115 profile25_node113_cert).mp (by decide +kernel))

def profile25_node114_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 19 82 103 111 119 103 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 66 68 72 64 96 64) }] }

theorem profile25_node114 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,80] 6 103 profile25_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,80] 6 103 profile25_node114_cert).mp (by decide +kernel))

def profile25_node115_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 19 98 87 95 87 119 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile25_node115 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,96] 6 87 profile25_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18,96] 6 87 profile25_node115_cert).mp (by decide +kernel))

def profile25_node52_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node52_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node52 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile25_node52_route profile25_node52_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node53
  · exact profile25_node67
  · exact profile25_node68
  · exact profile25_node69
  · exact profile25_node76
  · exact profile25_node83
  · exact profile25_node84
  · exact profile25_node113
  · exact profile25_node114
  · exact profile25_node115

def profile25_node117_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 21 19 103 107 115 99 64), lower := (rows 21 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 69 111 68 72 64 96 64) }] }

theorem profile25_node117 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,17] 6 99 profile25_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,17] 6 99 profile25_node117_cert).mp (by decide +kernel))

def profile25_node119_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 21 35 7 90 82 114 64), lower := (rows 21 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 124 122 126 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 69 103 71 72 64 96 64) }] }

theorem profile25_node119 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,3] 6 82 profile25_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,3] 6 82 profile25_node119_cert).mp (by decide +kernel))

def profile25_node120_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 21 35 21 74 82 98 64), lower := (rows 21 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 84 122 84 72 80 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node120 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,17] 6 66 profile25_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,17] 6 66 profile25_node120_cert).mp (by decide +kernel))

def profile25_node121_cert : CutBound 7 := { lost := (rows 2 16 0 16 0 0 0), upper := (rows 21 35 22 75 83 99 64), lower := (rows 21 35 22 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 32 127), good := (rows 85 97 85 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 111 107 110 72 64 96 64) }] }

theorem profile25_node121 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,18] 6 67 profile25_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,18] 6 67 profile25_node121_cert).mp (by decide +kernel))

def profile25_node122_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 21 35 69 90 82 114 64), lower := (rows 21 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 84 122 68 72 80 96 64) },{ target := 1, region := (rows 17 0 23 8 16 32 127), good := (rows 85 101 69 72 85 96 64) }] }

theorem profile25_node122 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,65] 6 82 profile25_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,65] 6 82 profile25_node122_cert).mp (by decide +kernel))

def profile25_node123_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 21 35 70 91 83 115 64), lower := (rows 21 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 84 102 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 69 103 70 72 64 96 64) }] }

theorem profile25_node123 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,66] 6 83 profile25_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,66] 6 83 profile25_node123_cert).mp (by decide +kernel))

def profile25_node124_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 21 35 84 75 83 99 64), lower := (rows 21 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node124 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,80] 6 67 profile25_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33,80] 6 67 profile25_node124_cert).mp (by decide +kernel))

def profile25_node118_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node118_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node118 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node118_route profile25_node118_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node119
  · exact profile25_node120
  · exact profile25_node121
  · exact profile25_node122
  · exact profile25_node123
  · exact profile25_node124

def profile25_node126_cert : CutBound 7 := { lost := (rows 64 0 64 16 0 0 0), upper := (rows 21 50 7 75 83 99 64), lower := (rows 21 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 109 98 111 72 64 96 64) },{ target := 6, region := (rows 3 2 6 8 16 32 0), good := (rows 21 55 7 8 16 32 0) }] }

theorem profile25_node126 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,3] 6 67 profile25_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,3] 6 67 profile25_node126_cert).mp (by decide +kernel))

def profile25_node127_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 21 50 69 75 83 99 64), lower := (rows 21 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 32 127), good := (rows 85 117 69 72 85 96 64) }] }

theorem profile25_node127 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,65] 6 67 profile25_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,65] 6 67 profile25_node127_cert).mp (by decide +kernel))

def profile25_node128_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 21 50 70 75 83 99 64), lower := (rows 21 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 84 118 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 69 102 70 72 64 96 64) }] }

theorem profile25_node128 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,66] 6 67 profile25_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48,66] 6 67 profile25_node128_cert).mp (by decide +kernel))

def profile25_node125_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node125_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node125 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,48] 6 (by decide) (choices 2) [3,65,66] profile25_node125_route profile25_node125_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node126
  · exact profile25_node127
  · exact profile25_node128

def profile25_node130_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 21 67 7 122 114 114 64), lower := (rows 21 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 124 122 126 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile25_node130 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,3] 6 114 profile25_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,3] 6 114 profile25_node130_cert).mp (by decide +kernel))


#print axioms profile25_node130
end Delivery.SmallBudgetTenFinite7
