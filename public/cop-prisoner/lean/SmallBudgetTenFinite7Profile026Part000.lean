import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile26_node3_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 11 21 120 112 112 64), lower := (rows 7 11 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node3 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,17] 6 112 profile26_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,17] 6 112 profile26_node3_cert).mp (by decide +kernel))

def profile26_node4_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 11 37 88 80 112 64), lower := (rows 7 11 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node4 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,33] 6 80 profile26_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,33] 6 80 profile26_node4_cert).mp (by decide +kernel))

def profile26_node6_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 11 52 25 80 96 64), lower := (rows 7 11 52 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 126 116 124 116 116 116) }] }

theorem profile26_node6 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,17] 6 64 profile26_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,17] 6 64 profile26_node6_cert).mp (by decide +kernel))

def profile26_node7_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 11 52 73 80 112 64), lower := (rows 7 11 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 126 116 124 116 116 116) }] }

theorem profile26_node7 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,65] 6 80 profile26_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,65] 6 80 profile26_node7_cert).mp (by decide +kernel))

def profile26_node8_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 11 52 88 81 97 64), lower := (rows 7 11 52 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 127), good := (rows 78 74 124 88 88 96 64) }] }

theorem profile26_node8 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,80] 6 65 profile26_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48,80] 6 65 profile26_node8_cert).mp (by decide +kernel))

def profile26_node5_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node5 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,48] 6 (by decide) (choices 2) [17,65,80] profile26_node5_route profile26_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node6
  · exact profile26_node7
  · exact profile26_node8

def profile26_node9_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 11 69 120 112 112 64), lower := (rows 7 11 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node9 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,65] 6 112 profile26_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,65] 6 112 profile26_node9_cert).mp (by decide +kernel))

def profile26_node10_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 11 84 121 113 113 64), lower := (rows 7 11 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 70 74 84 72 84 96 64) }] }

theorem profile26_node10 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,80] 6 113 profile26_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,80] 6 113 profile26_node10_cert).mp (by decide +kernel))

def profile26_node11_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 11 100 89 81 113 64), lower := (rows 7 11 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 70 74 100 72 80 100 64) }] }

theorem profile26_node11 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,96] 6 81 profile26_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9,96] 6 81 profile26_node11_cert).mp (by decide +kernel))

def profile26_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile26_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node2 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,9] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile26_node2_route profile26_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node3
  · exact profile26_node4
  · exact profile26_node5
  · exact profile26_node9
  · exact profile26_node10
  · exact profile26_node11

def profile26_node13_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 13 120 112 112 64), lower := (rows 7 19 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node13 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,9] 6 112 profile26_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,9] 6 112 profile26_node13_cert).mp (by decide +kernel))

def profile26_node14_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 21 104 120 104 64), lower := (rows 7 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node14 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,17] 6 104 profile26_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,17] 6 104 profile26_node14_cert).mp (by decide +kernel))

def profile26_node15_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 19 28 105 113 97 64), lower := (rows 7 19 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 111 107 76 72 64 96 64) }] }

theorem profile26_node15 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,24] 6 97 profile26_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,24] 6 97 profile26_node15_cert).mp (by decide +kernel))

def profile26_node16_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 37 88 88 120 64), lower := (rows 7 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node16 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,33] 6 88 profile26_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,33] 6 88 profile26_node16_cert).mp (by decide +kernel))

def profile26_node18_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 44 25 80 96 64), lower := (rows 7 19 44 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 118 114 124 124 112 112 112) }] }

theorem profile26_node18 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,17] 6 64 profile26_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,17] 6 64 profile26_node18_cert).mp (by decide +kernel))

def profile26_node19_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 44 73 80 112 64), lower := (rows 7 19 44 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 118 114 124 124 112 112 112) }] }

theorem profile26_node19 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,65] 6 80 profile26_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,65] 6 80 profile26_node19_cert).mp (by decide +kernel))

def profile26_node20_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 44 88 81 97 64), lower := (rows 7 19 44 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 78 90 108 88 88 96 64) }] }

theorem profile26_node20 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,80] 6 65 profile26_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40,80] 6 65 profile26_node20_cert).mp (by decide +kernel))

def profile26_node17_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node17_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node17 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,40] 6 (by decide) (choices 2) [17,65,80] profile26_node17_route profile26_node17_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node18
  · exact profile26_node19
  · exact profile26_node20

def profile26_node21_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 19 52 73 89 105 64), lower := (rows 7 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 111 107 100 72 64 96 64) }] }

theorem profile26_node21 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,48] 6 73 profile26_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,48] 6 73 profile26_node21_cert).mp (by decide +kernel))

def profile26_node22_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 19 69 120 120 120 64), lower := (rows 7 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node22 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,65] 6 120 profile26_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,65] 6 120 profile26_node22_cert).mp (by decide +kernel))

def profile26_node23_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 76 121 113 113 64), lower := (rows 7 19 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 70 82 76 76 80 96 64) }] }

theorem profile26_node23 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,72] 6 113 profile26_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,72] 6 113 profile26_node23_cert).mp (by decide +kernel))

def profile26_node24_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 84 105 121 105 64), lower := (rows 7 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 86 84 72 84 96 64) }] }

theorem profile26_node24 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,80] 6 105 profile26_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,80] 6 105 profile26_node24_cert).mp (by decide +kernel))

def profile26_node25_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 19 100 89 89 121 64), lower := (rows 7 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 70 82 100 72 80 100 64) }] }

theorem profile26_node25 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,96] 6 89 profile26_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17,96] 6 89 profile26_node25_cert).mp (by decide +kernel))

def profile26_node12_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile26_node12_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node12 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,17] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile26_node12_route profile26_node12_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node13
  · exact profile26_node14
  · exact profile26_node15
  · exact profile26_node16
  · exact profile26_node17
  · exact profile26_node21
  · exact profile26_node22
  · exact profile26_node23
  · exact profile26_node24
  · exact profile26_node25

def profile26_node27_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 26 21 105 113 97 64), lower := (rows 7 26 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 111 74 109 72 64 96 64) }] }

theorem profile26_node27 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,17] 6 97 profile26_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,17] 6 97 profile26_node27_cert).mp (by decide +kernel))

def profile26_node29_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 26 37 25 80 96 64), lower := (rows 7 26 37 25 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 127 127 127), good := (rows 118 122 116 122 112 112 112) }] }

theorem profile26_node29 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,17] 6 64 profile26_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,17] 6 64 profile26_node29_cert).mp (by decide +kernel))

def profile26_node30_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 26 37 73 80 112 64), lower := (rows 7 26 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 127 127 127), good := (rows 118 122 116 122 112 112 112) }] }

theorem profile26_node30 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,65] 6 80 profile26_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,65] 6 80 profile26_node30_cert).mp (by decide +kernel))

def profile26_node31_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 26 37 88 81 97 64), lower := (rows 7 26 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 78 90 100 90 90 96 64) }] }

theorem profile26_node31 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,80] 6 65 profile26_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33,80] 6 65 profile26_node31_cert).mp (by decide +kernel))

def profile26_node28_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node28_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node28 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,33] 6 (by decide) (choices 2) [17,65,80] profile26_node28_route profile26_node28_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node29
  · exact profile26_node30
  · exact profile26_node31

def profile26_node32_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 26 52 73 81 97 64), lower := (rows 7 26 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 74 100 72 64 96 64) }] }

theorem profile26_node32 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,48] 6 65 profile26_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,48] 6 65 profile26_node32_cert).mp (by decide +kernel))

def profile26_node33_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 26 69 121 113 113 64), lower := (rows 7 26 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 79 69 72 64 96 64) }] }

theorem profile26_node33 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,65] 6 113 profile26_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,65] 6 113 profile26_node33_cert).mp (by decide +kernel))

def profile26_node34_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 26 84 105 113 97 64), lower := (rows 7 26 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 94 84 72 84 96 64) }] }

theorem profile26_node34 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,80] 6 97 profile26_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,80] 6 97 profile26_node34_cert).mp (by decide +kernel))

def profile26_node35_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 26 100 89 81 113 64), lower := (rows 7 26 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 70 90 100 72 80 100 64) }] }

theorem profile26_node35 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,96] 6 81 profile26_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24,96] 6 81 profile26_node35_cert).mp (by decide +kernel))

def profile26_node26_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile26_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node26 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,24] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile26_node26_route profile26_node26_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node27
  · exact profile26_node28
  · exact profile26_node32
  · exact profile26_node33
  · exact profile26_node34
  · exact profile26_node35

def profile26_node37_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 35 13 88 80 112 64), lower := (rows 7 35 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node37 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,9] 6 80 profile26_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,9] 6 80 profile26_node37_cert).mp (by decide +kernel))

def profile26_node38_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 35 21 88 88 120 64), lower := (rows 7 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node38 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,17] 6 88 profile26_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,17] 6 88 profile26_node38_cert).mp (by decide +kernel))

def profile26_node40_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 35 28 25 80 96 64), lower := (rows 7 35 28 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 118 114 124 124 112 112 112) }] }

theorem profile26_node40 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,17] 6 64 profile26_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,17] 6 64 profile26_node40_cert).mp (by decide +kernel))

def profile26_node41_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 35 28 73 80 112 64), lower := (rows 7 35 28 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 118 114 124 124 112 112 112) }] }

theorem profile26_node41 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,65] 6 80 profile26_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,65] 6 80 profile26_node41_cert).mp (by decide +kernel))

def profile26_node42_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 7 35 28 88 81 97 64), lower := (rows 7 35 28 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 28 28 16 32 127), good := (rows 78 98 92 92 92 96 64) }] }

theorem profile26_node42 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,80] 6 65 profile26_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24,80] 6 65 profile26_node42_cert).mp (by decide +kernel))

def profile26_node39_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node39_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node39 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,24] 6 (by decide) (choices 2) [17,65,80] profile26_node39_route profile26_node39_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node40
  · exact profile26_node41
  · exact profile26_node42

def profile26_node43_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 35 69 88 88 120 64), lower := (rows 7 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile26_node43 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,65] 6 88 profile26_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,65] 6 88 profile26_node43_cert).mp (by decide +kernel))

def profile26_node44_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 35 76 89 81 113 64), lower := (rows 7 35 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 70 98 76 76 80 96 64) }] }

theorem profile26_node44 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,72] 6 81 profile26_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,72] 6 81 profile26_node44_cert).mp (by decide +kernel))

def profile26_node45_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 35 84 89 89 121 64), lower := (rows 7 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 70 98 84 72 84 96 64) }] }

theorem profile26_node45 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,80] 6 89 profile26_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33,80] 6 89 profile26_node45_cert).mp (by decide +kernel))

def profile26_node36_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node36_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node36 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,33] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node36_route profile26_node36_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node37
  · exact profile26_node38
  · exact profile26_node39
  · exact profile26_node43
  · exact profile26_node44
  · exact profile26_node45

def profile26_node48_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 42 21 25 80 96 64), lower := (rows 7 42 21 25 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 127 127 127), good := (rows 118 122 116 122 112 112 112) }] }

theorem profile26_node48 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,17] 6 64 profile26_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,17] 6 64 profile26_node48_cert).mp (by decide +kernel))

def profile26_node49_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 42 21 73 80 112 64), lower := (rows 7 42 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 127 127 127), good := (rows 118 122 116 122 112 112 112) }] }

theorem profile26_node49 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,65] 6 80 profile26_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,65] 6 80 profile26_node49_cert).mp (by decide +kernel))

def profile26_node50_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 42 21 88 81 97 64), lower := (rows 7 42 21 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 127), good := (rows 78 106 92 88 88 96 64) }] }

theorem profile26_node50 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,80] 6 65 profile26_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17,80] 6 65 profile26_node50_cert).mp (by decide +kernel))

def profile26_node47_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node47_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node47 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,17] 6 (by decide) (choices 2) [17,65,80] profile26_node47_route profile26_node47_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node48
  · exact profile26_node49
  · exact profile26_node50

def profile26_node51_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 42 69 89 81 113 64), lower := (rows 7 42 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 111 69 72 64 96 64) }] }

theorem profile26_node51 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,65] 6 81 profile26_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,65] 6 81 profile26_node51_cert).mp (by decide +kernel))

def profile26_node52_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 42 84 89 81 113 64), lower := (rows 7 42 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 70 106 84 72 84 96 64) }] }

theorem profile26_node52 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,80] 6 81 profile26_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40,80] 6 81 profile26_node52_cert).mp (by decide +kernel))

def profile26_node46_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node46_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node46 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,40] 6 (by decide) (choices 2) [17,65,80] profile26_node46_route profile26_node46_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node47
  · exact profile26_node51
  · exact profile26_node52

def profile26_node55_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 50 13 25 80 96 64), lower := (rows 7 50 13 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) }] }

theorem profile26_node55 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,17] 6 64 profile26_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,17] 6 64 profile26_node55_cert).mp (by decide +kernel))

def profile26_node56_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 50 13 73 80 112 64), lower := (rows 7 50 13 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) }] }

theorem profile26_node56 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,65] 6 80 profile26_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,65] 6 80 profile26_node56_cert).mp (by decide +kernel))

def profile26_node57_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 7 50 13 88 81 97 64), lower := (rows 7 50 13 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 78 122 76 88 88 96 64) }] }

theorem profile26_node57 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,80] 6 65 profile26_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9,80] 6 65 profile26_node57_cert).mp (by decide +kernel))

def profile26_node54_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node54_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node54 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,9] 6 (by decide) (choices 2) [17,65,80] profile26_node54_route profile26_node54_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node55
  · exact profile26_node56
  · exact profile26_node57

def profile26_node58_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 50 21 73 89 105 64), lower := (rows 7 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 111 98 109 72 64 96 64) }] }

theorem profile26_node58 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,17] 6 73 profile26_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,17] 6 73 profile26_node58_cert).mp (by decide +kernel))

def profile26_node59_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 7 50 28 73 81 97 64), lower := (rows 7 50 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 76 72 64 96 64) }] }

theorem profile26_node59 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,24] 6 65 profile26_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,24] 6 65 profile26_node59_cert).mp (by decide +kernel))

def profile26_node60_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 7 50 69 89 89 121 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile26_node60 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,65] 6 89 profile26_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,65] 6 89 profile26_node60_cert).mp (by decide +kernel))

def profile26_node61_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 50 76 89 81 113 64), lower := (rows 7 50 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 70 114 76 76 80 96 64) }] }

theorem profile26_node61 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,72] 6 81 profile26_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,72] 6 81 profile26_node61_cert).mp (by decide +kernel))

def profile26_node62_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 50 84 73 89 105 64), lower := (rows 7 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) }] }

theorem profile26_node62 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,80] 6 73 profile26_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48,80] 6 73 profile26_node62_cert).mp (by decide +kernel))

def profile26_node53_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node53_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node53 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,48] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node53_route profile26_node53_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node54
  · exact profile26_node58
  · exact profile26_node59
  · exact profile26_node60
  · exact profile26_node61
  · exact profile26_node62

def profile26_node63_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 7 67 125 121 121 121 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 127), good := (rows 71 67 71 72 64 96 64) }] }

theorem profile26_node63 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,65] 6 121 profile26_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,65] 6 121 profile26_node63_cert).mp (by decide +kernel))

def profile26_node64_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 74 117 121 113 113 64), lower := (rows 7 74 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 127), good := (rows 70 74 68 74 80 96 64) }] }

theorem profile26_node64 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,72] 6 113 profile26_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,72] 6 113 profile26_node64_cert).mp (by decide +kernel))

def profile26_node65_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 82 125 121 121 121 64), lower := (rows 7 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 68 72 82 96 64) }] }

theorem profile26_node65 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,80] 6 121 profile26_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,80] 6 121 profile26_node65_cert).mp (by decide +kernel))

def profile26_node66_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 98 93 89 89 121 64), lower := (rows 7 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 70 98 68 72 80 98 64) }] }

theorem profile26_node66 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,96] 6 89 profile26_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6,96] 6 89 profile26_node66_cert).mp (by decide +kernel))

def profile26_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile26_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [6] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile26_node1_route profile26_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node2
  · exact profile26_node12
  · exact profile26_node26
  · exact profile26_node36
  · exact profile26_node46
  · exact profile26_node53
  · exact profile26_node63
  · exact profile26_node64
  · exact profile26_node65
  · exact profile26_node66

def profile26_node69_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 13 120 112 112 64), lower := (rows 19 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node69 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,9] 6 112 profile26_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,9] 6 112 profile26_node69_cert).mp (by decide +kernel))

def profile26_node70_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 21 104 120 104 64), lower := (rows 19 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node70 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,17] 6 104 profile26_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,17] 6 104 profile26_node70_cert).mp (by decide +kernel))

def profile26_node71_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 19 7 28 105 113 97 64), lower := (rows 19 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 107 111 76 72 64 96 64) }] }

theorem profile26_node71 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,24] 6 97 profile26_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,24] 6 97 profile26_node71_cert).mp (by decide +kernel))

def profile26_node72_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 37 88 88 120 64), lower := (rows 19 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node72 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,33] 6 88 profile26_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,33] 6 88 profile26_node72_cert).mp (by decide +kernel))

def profile26_node74_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 44 25 80 96 64), lower := (rows 19 7 44 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 118 124 124 112 112 112) }] }

theorem profile26_node74 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,17] 6 64 profile26_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,17] 6 64 profile26_node74_cert).mp (by decide +kernel))

def profile26_node75_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 44 73 80 112 64), lower := (rows 19 7 44 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 118 124 124 112 112 112) }] }

theorem profile26_node75 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,65] 6 80 profile26_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,65] 6 80 profile26_node75_cert).mp (by decide +kernel))

def profile26_node76_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 44 88 81 97 64), lower := (rows 19 7 44 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 78 108 88 88 96 64) }] }

theorem profile26_node76 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,80] 6 65 profile26_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40,80] 6 65 profile26_node76_cert).mp (by decide +kernel))

def profile26_node73_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node73_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node73 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,40] 6 (by decide) (choices 2) [17,65,80] profile26_node73_route profile26_node73_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node74
  · exact profile26_node75
  · exact profile26_node76

def profile26_node77_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 19 7 52 73 89 105 64), lower := (rows 19 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 107 111 100 72 64 96 64) }] }

theorem profile26_node77 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,48] 6 73 profile26_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,48] 6 73 profile26_node77_cert).mp (by decide +kernel))

def profile26_node78_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 7 69 120 120 120 64), lower := (rows 19 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node78 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,65] 6 120 profile26_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,65] 6 120 profile26_node78_cert).mp (by decide +kernel))

def profile26_node79_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 76 121 113 113 64), lower := (rows 19 7 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 82 70 76 76 80 96 64) }] }

theorem profile26_node79 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,72] 6 113 profile26_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,72] 6 113 profile26_node79_cert).mp (by decide +kernel))

def profile26_node80_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 84 105 121 105 64), lower := (rows 19 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 70 84 72 84 96 64) }] }

theorem profile26_node80 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,80] 6 105 profile26_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,80] 6 105 profile26_node80_cert).mp (by decide +kernel))

def profile26_node81_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 7 100 89 89 121 64), lower := (rows 19 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 70 100 72 80 100 64) }] }

theorem profile26_node81 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,96] 6 89 profile26_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5,96] 6 89 profile26_node81_cert).mp (by decide +kernel))

def profile26_node68_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile26_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node68 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,5] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile26_node68_route profile26_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node69
  · exact profile26_node70
  · exact profile26_node71
  · exact profile26_node72
  · exact profile26_node73
  · exact profile26_node77
  · exact profile26_node78
  · exact profile26_node79
  · exact profile26_node80
  · exact profile26_node81

def profile26_node83_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 14 21 105 113 97 64), lower := (rows 19 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 13 0 37 127), good := (rows 107 110 111 72 64 96 64) }] }

theorem profile26_node83 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,17] 6 97 profile26_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,17] 6 97 profile26_node83_cert).mp (by decide +kernel))

def profile26_node85_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 14 37 25 80 96 64), lower := (rows 19 14 37 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 13 8 0 127 127), good := (rows 103 110 101 111 96 96 96) }] }

theorem profile26_node85 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,17] 6 64 profile26_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,17] 6 64 profile26_node85_cert).mp (by decide +kernel))

def profile26_node86_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 14 37 73 80 112 64), lower := (rows 19 14 37 73 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 13 0 32 127), good := (rows 75 78 111 73 64 96 64) }] }

theorem profile26_node86 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,65] 6 80 profile26_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,65] 6 80 profile26_node86_cert).mp (by decide +kernel))

def profile26_node87_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 19 14 37 88 81 97 64), lower := (rows 19 14 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 25 16 32 127), good := (rows 90 78 110 88 88 96 64) }] }

theorem profile26_node87 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,80] 6 65 profile26_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33,80] 6 65 profile26_node87_cert).mp (by decide +kernel))

def profile26_node84_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node84_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node84 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,33] 6 (by decide) (choices 2) [17,65,80] profile26_node84_route profile26_node84_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node85
  · exact profile26_node86
  · exact profile26_node87

def profile26_node88_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 19 14 52 73 81 97 64), lower := (rows 19 14 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 107 78 100 72 64 96 64) }] }

theorem profile26_node88 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,48] 6 65 profile26_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,48] 6 65 profile26_node88_cert).mp (by decide +kernel))

def profile26_node89_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 19 14 69 121 113 113 64), lower := (rows 19 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 78 69 72 64 96 64) }] }

theorem profile26_node89 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,65] 6 113 profile26_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,65] 6 113 profile26_node89_cert).mp (by decide +kernel))

def profile26_node90_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 14 84 105 113 97 64), lower := (rows 19 14 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 78 84 72 84 96 64) }] }

theorem profile26_node90 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,80] 6 97 profile26_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,80] 6 97 profile26_node90_cert).mp (by decide +kernel))

def profile26_node91_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 14 100 89 81 113 64), lower := (rows 19 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 78 100 72 80 100 64) }] }

theorem profile26_node91 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,96] 6 81 profile26_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12,96] 6 81 profile26_node91_cert).mp (by decide +kernel))

def profile26_node82_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile26_node82_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node82 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,12] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile26_node82_route profile26_node82_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node83
  · exact profile26_node84
  · exact profile26_node88
  · exact profile26_node89
  · exact profile26_node90
  · exact profile26_node91

def profile26_node92_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 19 109 109 125 109 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) }] }

theorem profile26_node92 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,17] 6 109 profile26_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,17] 6 109 profile26_node92_cert).mp (by decide +kernel))

def profile26_node93_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 22 109 105 121 105 64), lower := (rows 19 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 70 68 72 64 96 64) }] }

theorem profile26_node93 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,20] 6 105 profile26_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,20] 6 105 profile26_node93_cert).mp (by decide +kernel))

def profile26_node95_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 35 13 92 84 116 64), lower := (rows 19 35 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) }] }

theorem profile26_node95 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,9] 6 84 profile26_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,9] 6 84 profile26_node95_cert).mp (by decide +kernel))

def profile26_node96_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 35 21 76 92 108 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) }] }

theorem profile26_node96 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,17] 6 76 profile26_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,17] 6 76 profile26_node96_cert).mp (by decide +kernel))

def profile26_node98_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 28 13 80 96 64), lower := (rows 19 35 28 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 114 124 124 112 112 112) }] }

theorem profile26_node98 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,5] 6 64 profile26_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,5] 6 64 profile26_node98_cert).mp (by decide +kernel))

def profile26_node99_cert : Bound 7 := { allowed := (rows 64 80 65 16 0 0 0), upper := (rows 19 35 28 73 84 100 64), lower := (rows 19 35 28 73 16 32 64), losses := [] }

theorem profile26_node99 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,65] 6 68 profile26_node99_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,65] 6 68 profile26_node99_cert).mp (by decide +kernel))

def profile26_node100_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 19 35 28 76 81 97 64), lower := (rows 19 35 28 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 31 16 32 127), good := (rows 94 110 92 76 92 96 64) }] }

theorem profile26_node100 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,68] 6 65 profile26_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24,68] 6 65 profile26_node100_cert).mp (by decide +kernel))

def profile26_node97_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node97_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node97 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,24] 6 (by decide) (choices 2) [5,65,68] profile26_node97_route profile26_node97_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node98
  · exact profile26_node99
  · exact profile26_node100

def profile26_node101_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 35 69 92 92 124 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) }] }

theorem profile26_node101 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,65] 6 92 profile26_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,65] 6 92 profile26_node101_cert).mp (by decide +kernel))

def profile26_node102_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 76 93 85 117 64), lower := (rows 19 35 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 82 98 76 76 80 96 64) }] }

theorem profile26_node102 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,72] 6 85 profile26_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,72] 6 85 profile26_node102_cert).mp (by decide +kernel))

def profile26_node103_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 35 84 77 93 109 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) }] }

theorem profile26_node103 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,80] 6 77 profile26_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33,80] 6 77 profile26_node103_cert).mp (by decide +kernel))

def profile26_node94_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node94_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node94 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,33] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node94_route profile26_node94_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node95
  · exact profile26_node96
  · exact profile26_node97
  · exact profile26_node101
  · exact profile26_node102
  · exact profile26_node103

def profile26_node106_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 38 13 25 80 96 64), lower := (rows 19 38 13 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 126 120 112 112 112) }] }

theorem profile26_node106 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,17] 6 64 profile26_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,17] 6 64 profile26_node106_cert).mp (by decide +kernel))

def profile26_node107_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 38 13 73 80 112 64), lower := (rows 19 38 13 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 126 120 112 112 112) }] }

theorem profile26_node107 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,65] 6 80 profile26_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,65] 6 80 profile26_node107_cert).mp (by decide +kernel))

def profile26_node108_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 19 38 13 88 81 97 64), lower := (rows 19 38 13 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 102 76 88 88 96 64) }] }

theorem profile26_node108 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,80] 6 65 profile26_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9,80] 6 65 profile26_node108_cert).mp (by decide +kernel))

def profile26_node105_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node105_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node105 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,9] 6 (by decide) (choices 2) [17,65,80] profile26_node105_route profile26_node105_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node106
  · exact profile26_node107
  · exact profile26_node108

def profile26_node109_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 38 21 73 89 105 64), lower := (rows 19 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 13 0 37 127), good := (rows 107 110 111 72 64 96 64) }] }

theorem profile26_node109 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,17] 6 73 profile26_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,17] 6 73 profile26_node109_cert).mp (by decide +kernel))

def profile26_node110_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 19 38 28 73 81 97 64), lower := (rows 19 38 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 107 102 76 72 64 96 64) }] }

theorem profile26_node110 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,24] 6 65 profile26_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,24] 6 65 profile26_node110_cert).mp (by decide +kernel))

def profile26_node111_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 19 38 69 89 89 121 64), lower := (rows 19 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 102 69 72 64 96 64) }] }

theorem profile26_node111 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,65] 6 89 profile26_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,65] 6 89 profile26_node111_cert).mp (by decide +kernel))

def profile26_node112_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 38 76 89 81 113 64), lower := (rows 19 38 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 82 102 76 76 80 96 64) }] }

theorem profile26_node112 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,72] 6 81 profile26_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,72] 6 81 profile26_node112_cert).mp (by decide +kernel))

def profile26_node113_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 19 38 84 73 89 105 64), lower := (rows 19 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) }] }

theorem profile26_node113 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,80] 6 73 profile26_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36,80] 6 73 profile26_node113_cert).mp (by decide +kernel))

def profile26_node104_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node104_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node104 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,36] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node104_route profile26_node104_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node105
  · exact profile26_node109
  · exact profile26_node110
  · exact profile26_node111
  · exact profile26_node112
  · exact profile26_node113

def profile26_node114_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 77 77 93 109 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) }] }

theorem profile26_node114 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,48] 6 77 profile26_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,48] 6 77 profile26_node114_cert).mp (by decide +kernel))

def profile26_node115_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 19 67 125 125 125 125 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile26_node115 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,65] 6 125 profile26_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,65] 6 125 profile26_node115_cert).mp (by decide +kernel))

def profile26_node116_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 70 125 121 121 121 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 70 70 72 80 96 64) }] }

theorem profile26_node116 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,68] 6 121 profile26_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,68] 6 121 profile26_node116_cert).mp (by decide +kernel))

def profile26_node117_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 82 109 109 125 109 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) }] }

theorem profile26_node117 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,80] 6 109 profile26_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,80] 6 109 profile26_node117_cert).mp (by decide +kernel))

def profile26_node118_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 19 98 93 93 93 125 64), lower := (rows 19 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) }] }

theorem profile26_node118 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,96] 6 93 profile26_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18,96] 6 93 profile26_node118_cert).mp (by decide +kernel))

def profile26_node67_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile26_node67_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile26_node67 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [18] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,65,68,80,96] profile26_node67_route profile26_node67_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node68
  · exact profile26_node82
  · exact profile26_node92
  · exact profile26_node93
  · exact profile26_node94
  · exact profile26_node104
  · exact profile26_node114
  · exact profile26_node115
  · exact profile26_node116
  · exact profile26_node117
  · exact profile26_node118

def profile26_node121_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 7 13 88 80 112 64), lower := (rows 35 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node121 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,9] 6 80 profile26_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,9] 6 80 profile26_node121_cert).mp (by decide +kernel))

def profile26_node122_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 7 21 88 88 120 64), lower := (rows 35 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node122 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,17] 6 88 profile26_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,17] 6 88 profile26_node122_cert).mp (by decide +kernel))

def profile26_node124_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 7 28 25 80 96 64), lower := (rows 35 7 28 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 118 124 124 112 112 112) }] }

theorem profile26_node124 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,17] 6 64 profile26_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,17] 6 64 profile26_node124_cert).mp (by decide +kernel))

def profile26_node125_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 7 28 73 80 112 64), lower := (rows 35 7 28 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 118 124 124 112 112 112) }] }

theorem profile26_node125 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,65] 6 80 profile26_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,65] 6 80 profile26_node125_cert).mp (by decide +kernel))

def profile26_node126_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 35 7 28 88 81 97 64), lower := (rows 35 7 28 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 28 28 16 32 127), good := (rows 98 78 92 92 92 96 64) }] }

theorem profile26_node126 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,80] 6 65 profile26_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24,80] 6 65 profile26_node126_cert).mp (by decide +kernel))

def profile26_node123_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node123_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node123 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,24] 6 (by decide) (choices 2) [17,65,80] profile26_node123_route profile26_node123_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node124
  · exact profile26_node125
  · exact profile26_node126

def profile26_node127_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 7 69 88 88 120 64), lower := (rows 35 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) }] }

theorem profile26_node127 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,65] 6 88 profile26_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,65] 6 88 profile26_node127_cert).mp (by decide +kernel))

def profile26_node128_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 7 76 89 81 113 64), lower := (rows 35 7 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 98 70 76 76 80 96 64) }] }

theorem profile26_node128 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,72] 6 81 profile26_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,72] 6 81 profile26_node128_cert).mp (by decide +kernel))

def profile26_node129_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 7 84 89 89 121 64), lower := (rows 35 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 98 70 84 72 84 96 64) }] }

theorem profile26_node129 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,80] 6 89 profile26_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5,80] 6 89 profile26_node129_cert).mp (by decide +kernel))

def profile26_node120_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node120_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node120 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,5] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node120_route profile26_node120_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node121
  · exact profile26_node122
  · exact profile26_node123
  · exact profile26_node127
  · exact profile26_node128
  · exact profile26_node129


#print axioms profile26_node120
end Delivery.SmallBudgetTenFinite7
