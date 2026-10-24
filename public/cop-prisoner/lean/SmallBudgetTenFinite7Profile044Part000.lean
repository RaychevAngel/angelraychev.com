import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile44_node2_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 11 124 120 120 120 120), lower := (rows 25 11 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 64), good := (rows 11 11 4 8 0 32 64) }] }

theorem profile44_node2 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,9] 6 120 profile44_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,9] 6 120 profile44_node2_cert).mp (by decide +kernel))

def profile44_node3_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 19 108 104 120 104 104), lower := (rows 25 19 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64), good := (rows 19 19 4 0 16 32 64) }] }

theorem profile44_node3 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,17] 6 104 profile44_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,17] 6 104 profile44_node3_cert).mp (by decide +kernel))

def profile44_node4_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 25 26 109 105 121 105 105), lower := (rows 25 26 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 10 4 8 0 32 64) }] }

theorem profile44_node4 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,24] 6 105 profile44_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,24] 6 105 profile44_node4_cert).mp (by decide +kernel))

def profile44_node6_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 35 28 104 120 104 104), lower := (rows 25 35 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node6 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,24] 6 104 profile44_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,24] 6 104 profile44_node6_cert).mp (by decide +kernel))

def profile44_node7_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 35 44 88 88 120 88), lower := (rows 25 35 44 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile44_node7 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,40] 6 88 profile44_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,40] 6 88 profile44_node7_cert).mp (by decide +kernel))

def profile44_node8_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 35 52 72 88 104 72), lower := (rows 25 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node8 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,48] 6 72 profile44_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,48] 6 72 profile44_node8_cert).mp (by decide +kernel))

def profile44_node10_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 35 76 24 120 104 104), lower := (rows 25 35 76 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 13 8 0 45 77), good := (rows 111 103 108 108 0 32 64) }] }

theorem profile44_node10 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,16] 6 104 profile44_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,16] 6 104 profile44_node10_cert).mp (by decide +kernel))

def profile44_node11_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 25 35 76 40 88 120 88), lower := (rows 25 35 76 40 16 32 64), losses := [{ target := 5, region := (rows 13 2 13 8 29 0 77), good := (rows 93 87 93 93 16 0 64) }] }

theorem profile44_node11 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,32] 6 88 profile44_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,32] 6 88 profile44_node11_cert).mp (by decide +kernel))

def profile44_node12_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 25 35 76 72 56 56 120), lower := (rows 25 35 76 72 16 32 64), losses := [{ target := 4, region := (rows 1 2 76 76 0 32 64), good := (rows 13 35 76 76 0 32 76) }] }

theorem profile44_node12 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,64] 6 56 profile44_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72,64] 6 56 profile44_node12_cert).mp (by decide +kernel))

def profile44_node9_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile44_node9_route : Route 7 := (fun mask => (mask,id))

theorem profile44_node9 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,72] 6 (by decide) (choices 1) [16,32,64] profile44_node9_route profile44_node9_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile44_node10
  · exact profile44_node11
  · exact profile44_node12

def profile44_node13_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 35 84 104 120 104 104), lower := (rows 25 35 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node13 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,80] 6 104 profile44_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,80] 6 104 profile44_node13_cert).mp (by decide +kernel))

def profile44_node14_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 35 100 88 88 120 88), lower := (rows 25 35 100 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile44_node14 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,96] 6 88 profile44_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33,96] 6 88 profile44_node14_cert).mp (by decide +kernel))

def profile44_node5_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile44_node5 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,33] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile44_node5_route profile44_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node6
  · exact profile44_node7
  · exact profile44_node8
  · exact profile44_node9
  · exact profile44_node13
  · exact profile44_node14

def profile44_node16_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 25 42 13 120 112 112 112), lower := (rows 25 42 13 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 64), good := (rows 13 42 13 8 0 32 64) }] }

theorem profile44_node16 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,9] 6 112 profile44_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,9] 6 112 profile44_node16_cert).mp (by decide +kernel))

def profile44_node17_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 42 21 104 120 104 104), lower := (rows 25 42 21 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 21 34 21 0 16 32 64) }] }

theorem profile44_node17 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,17] 6 104 profile44_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,17] 6 104 profile44_node17_cert).mp (by decide +kernel))

def profile44_node18_cert : Bound 7 := { allowed := (rows 96 80 96 0 0 0 0), upper := (rows 25 42 28 105 113 97 97), lower := (rows 25 42 28 8 16 32 64), losses := [] }

theorem profile44_node18 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,24] 6 97 profile44_node18_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,24] 6 97 profile44_node18_cert).mp (by decide +kernel))

def profile44_node19_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 42 37 88 88 120 88), lower := (rows 25 42 37 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile44_node19 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,33] 6 88 profile44_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,33] 6 88 profile44_node19_cert).mp (by decide +kernel))

def profile44_node20_cert : Bound 7 := { allowed := (rows 96 80 80 0 0 0 0), upper := (rows 25 42 44 89 81 113 81), lower := (rows 25 42 44 8 16 32 64), losses := [] }

theorem profile44_node20 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,40] 6 81 profile44_node20_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,40] 6 81 profile44_node20_cert).mp (by decide +kernel))

def profile44_node21_cert : Bound 7 := { allowed := (rows 96 80 72 0 0 0 0), upper := (rows 25 42 52 73 89 105 73), lower := (rows 25 42 52 8 16 32 64), losses := [] }

theorem profile44_node21 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,48] 6 73 profile44_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,48] 6 73 profile44_node21_cert).mp (by decide +kernel))

def profile44_node23_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 69 24 120 104 104), lower := (rows 25 42 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 11 5 8 0 43 75), good := (rows 111 106 103 106 0 32 64) }] }

theorem profile44_node23 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,16] 6 104 profile44_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,16] 6 104 profile44_node23_cert).mp (by decide +kernel))

def profile44_node24_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 42 69 40 88 120 88), lower := (rows 25 42 69 40 16 32 64), losses := [{ target := 4, region := (rows 1 42 4 42 0 32 64), good := (rows 11 42 69 42 0 42 64) }] }

theorem profile44_node24 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,32] 6 88 profile44_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,32] 6 88 profile44_node24_cert).mp (by decide +kernel))

def profile44_node25_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 25 42 69 72 56 56 120), lower := (rows 25 42 69 72 16 32 64), losses := [{ target := 6, region := (rows 11 11 4 8 27 43 0), good := (rows 59 59 55 59 16 32 0) }] }

theorem profile44_node25 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,64] 6 56 profile44_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65,64] 6 56 profile44_node25_cert).mp (by decide +kernel))

def profile44_node22_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile44_node22_route : Route 7 := (fun mask => (mask,id))

theorem profile44_node22 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,65] 6 (by decide) (choices 1) [16,32,64] profile44_node22_route profile44_node22_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile44_node23
  · exact profile44_node24
  · exact profile44_node25

def profile44_node26_cert : Bound 7 := { allowed := (rows 96 80 48 0 0 0 0), upper := (rows 25 42 76 121 113 113 113), lower := (rows 25 42 76 8 16 32 64), losses := [] }

theorem profile44_node26 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,72] 6 113 profile44_node26_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,72] 6 113 profile44_node26_cert).mp (by decide +kernel))

def profile44_node27_cert : Bound 7 := { allowed := (rows 96 80 40 0 0 0 0), upper := (rows 25 42 84 105 121 105 105), lower := (rows 25 42 84 8 16 32 64), losses := [] }

theorem profile44_node27 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,80] 6 105 profile44_node27_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,80] 6 105 profile44_node27_cert).mp (by decide +kernel))

def profile44_node28_cert : Bound 7 := { allowed := (rows 96 80 24 0 0 0 0), upper := (rows 25 42 100 89 89 121 89), lower := (rows 25 42 100 8 16 32 64), losses := [] }

theorem profile44_node28 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,96] 6 89 profile44_node28_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40,96] 6 89 profile44_node28_cert).mp (by decide +kernel))

def profile44_node15_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile44_node15 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,40] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile44_node15_route profile44_node15_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node16
  · exact profile44_node17
  · exact profile44_node18
  · exact profile44_node19
  · exact profile44_node20
  · exact profile44_node21
  · exact profile44_node22
  · exact profile44_node26
  · exact profile44_node27
  · exact profile44_node28

def profile44_node29_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 25 50 109 105 121 105 105), lower := (rows 25 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 34 4 8 0 32 64) }] }

theorem profile44_node29 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,48] 6 105 profile44_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,48] 6 105 profile44_node29_cert).mp (by decide +kernel))

def profile44_node31_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 25 98 13 120 120 120 120), lower := (rows 25 98 13 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 64), good := (rows 13 98 13 8 0 32 64) }] }

theorem profile44_node31 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,9] 6 120 profile44_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,9] 6 120 profile44_node31_cert).mp (by decide +kernel))

def profile44_node32_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 98 21 104 120 104 104), lower := (rows 25 98 21 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 21 98 21 0 16 32 64) }] }

theorem profile44_node32 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,17] 6 104 profile44_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,17] 6 104 profile44_node32_cert).mp (by decide +kernel))

def profile44_node33_cert : Bound 7 := { allowed := (rows 96 24 96 0 0 0 0), upper := (rows 25 98 28 105 121 105 105), lower := (rows 25 98 28 8 16 32 64), losses := [] }

theorem profile44_node33 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,24] 6 105 profile44_node33_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,24] 6 105 profile44_node33_cert).mp (by decide +kernel))

def profile44_node34_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 98 37 88 88 120 88), lower := (rows 25 98 37 8 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile44_node34 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,33] 6 88 profile44_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,33] 6 88 profile44_node34_cert).mp (by decide +kernel))

def profile44_node35_cert : Bound 7 := { allowed := (rows 96 24 80 0 0 0 0), upper := (rows 25 98 44 89 89 121 89), lower := (rows 25 98 44 8 16 32 64), losses := [] }

theorem profile44_node35 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,40] 6 89 profile44_node35_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,40] 6 89 profile44_node35_cert).mp (by decide +kernel))

def profile44_node36_cert : Bound 7 := { allowed := (rows 96 24 72 0 0 0 0), upper := (rows 25 98 52 73 89 105 73), lower := (rows 25 98 52 8 16 32 64), losses := [] }

theorem profile44_node36 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,48] 6 73 profile44_node36_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,48] 6 73 profile44_node36_cert).mp (by decide +kernel))

def profile44_node37_cert : Bound 7 := { allowed := (rows 96 24 24 0 0 0 0), upper := (rows 25 98 100 25 25 57 89), lower := (rows 25 98 100 8 16 32 64), losses := [] }

theorem profile44_node37 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,96] 6 25 profile44_node37_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96,96] 6 25 profile44_node37_cert).mp (by decide +kernel))

def profile44_node30_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node30_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile44_node30 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24,96] 6 (by decide) (choices 2) [9,17,24,33,40,48,96] profile44_node30_route profile44_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node31
  · exact profile44_node32
  · exact profile44_node33
  · exact profile44_node34
  · exact profile44_node35
  · exact profile44_node36
  · exact profile44_node37

def profile44_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile44_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile44_node1 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [24] 6 (by decide) (choices 2) [9,17,24,33,40,48,96] profile44_node1_route profile44_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node2
  · exact profile44_node3
  · exact profile44_node4
  · exact profile44_node5
  · exact profile44_node15
  · exact profile44_node29
  · exact profile44_node30

def profile44_node40_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 11 28 104 120 104 104), lower := (rows 49 11 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node40 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,24] 6 104 profile44_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,24] 6 104 profile44_node40_cert).mp (by decide +kernel))

def profile44_node41_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 49 11 52 72 88 104 72), lower := (rows 49 11 52 8 16 32 64), losses := [{ target := 3, region := (rows 5 2 5 0 16 32 64), good := (rows 53 7 53 0 16 32 64) }] }

theorem profile44_node41 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,48] 6 72 profile44_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,48] 6 72 profile44_node41_cert).mp (by decide +kernel))

def profile44_node43_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 11 76 24 120 104 104), lower := (rows 49 11 76 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 14 8 0 46 78), good := (rows 33 111 108 108 0 32 64) }] }

theorem profile44_node43 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,16] 6 104 profile44_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,16] 6 104 profile44_node43_cert).mp (by decide +kernel))

def profile44_node44_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 11 76 72 56 56 120), lower := (rows 49 11 76 72 16 32 64), losses := [{ target := 4, region := (rows 1 2 76 76 0 32 64), good := (rows 33 15 76 76 0 32 76) }] }

theorem profile44_node44 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,64] 6 56 profile44_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72,64] 6 56 profile44_node44_cert).mp (by decide +kernel))

def profile44_node42_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile44_node42_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node42 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,72] 6 (by decide) (choices 1) [16,64] profile44_node42_route profile44_node42_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile44_node43
  · exact profile44_node44

def profile44_node45_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 11 84 104 120 104 104), lower := (rows 49 11 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node45 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,80] 6 104 profile44_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9,80] 6 104 profile44_node45_cert).mp (by decide +kernel))

def profile44_node39_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node39_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node39 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,9] 6 (by decide) (choices 2) [24,48,72,80] profile44_node39_route profile44_node39_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile44_node40
  · exact profile44_node41
  · exact profile44_node42
  · exact profile44_node45

def profile44_node46_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 49 19 108 104 120 104 104), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64), good := (rows 51 19 4 0 16 32 64) }] }

theorem profile44_node46 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,17] 6 104 profile44_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,17] 6 104 profile44_node46_cert).mp (by decide +kernel))

def profile44_node47_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 26 109 105 121 105 105), lower := (rows 49 26 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 10 4 8 0 32 64) }] }

theorem profile44_node47 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,24] 6 105 profile44_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,24] 6 105 profile44_node47_cert).mp (by decide +kernel))

def profile44_node48_cert : CutBound 7 := { lost := (rows 8 8 0 0 0 0 0), upper := (rows 49 50 77 73 89 105 73), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 3, region := (rows 3 3 4 0 16 32 64), good := (rows 51 51 4 0 16 32 64) }] }

theorem profile44_node48 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,48] 6 73 profile44_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,48] 6 73 profile44_node48_cert).mp (by decide +kernel))

def profile44_node50_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 28 104 120 104 104), lower := (rows 49 67 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node50 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,24] 6 104 profile44_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,24] 6 104 profile44_node50_cert).mp (by decide +kernel))

def profile44_node51_cert : CutBound 7 := { lost := (rows 8 0 8 0 0 0 0), upper := (rows 49 67 52 72 88 104 72), lower := (rows 49 67 52 8 16 32 64), losses := [{ target := 3, region := (rows 5 2 5 0 16 32 64), good := (rows 53 71 53 0 16 32 64) }] }

theorem profile44_node51 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,48] 6 72 profile44_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,48] 6 72 profile44_node51_cert).mp (by decide +kernel))

def profile44_node52_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 49 67 76 56 56 56 120), lower := (rows 49 67 76 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile44_node52 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,72] 6 56 profile44_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,72] 6 56 profile44_node52_cert).mp (by decide +kernel))

def profile44_node53_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 84 40 56 40 104), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile44_node53 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,80] 6 40 profile44_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65,80] 6 40 profile44_node53_cert).mp (by decide +kernel))

def profile44_node49_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node49_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node49 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,65] 6 (by decide) (choices 2) [24,48,72,80] profile44_node49_route profile44_node49_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile44_node50
  · exact profile44_node51
  · exact profile44_node52
  · exact profile44_node53

def profile44_node56_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 74 13 24 120 104 104), lower := (rows 49 74 13 24 16 32 64), losses := [{ target := 4, region := (rows 1 14 4 8 0 46 78), good := (rows 33 106 111 106 0 32 64) }] }

theorem profile44_node56 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,16] 6 104 profile44_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,16] 6 104 profile44_node56_cert).mp (by decide +kernel))

def profile44_node57_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 74 13 72 56 56 120), lower := (rows 49 74 13 72 16 32 64), losses := [{ target := 4, region := (rows 1 74 4 74 0 32 64), good := (rows 33 74 15 74 0 32 74) }] }

theorem profile44_node57 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,64] 6 56 profile44_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9,64] 6 56 profile44_node57_cert).mp (by decide +kernel))

def profile44_node55_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile44_node55_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node55 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,9] 6 (by decide) (choices 1) [16,64] profile44_node55_route profile44_node55_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile44_node56
  · exact profile44_node57

def profile44_node58_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 49 74 21 104 120 104 104), lower := (rows 49 74 21 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64), good := (rows 53 66 21 0 16 32 64) }] }

theorem profile44_node58 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,17] 6 104 profile44_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,17] 6 104 profile44_node58_cert).mp (by decide +kernel))

def profile44_node59_cert : Bound 7 := { allowed := (rows 72 48 96 0 0 0 0), upper := (rows 49 74 28 105 121 105 105), lower := (rows 49 74 28 8 16 32 64), losses := [] }

theorem profile44_node59 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,24] 6 105 profile44_node59_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,24] 6 105 profile44_node59_cert).mp (by decide +kernel))

def profile44_node60_cert : Bound 7 := { allowed := (rows 72 48 72 0 0 0 0), upper := (rows 49 74 52 73 89 105 73), lower := (rows 49 74 52 8 16 32 64), losses := [] }

theorem profile44_node60 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,48] 6 73 profile44_node60_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,48] 6 73 profile44_node60_cert).mp (by decide +kernel))

def profile44_node61_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 49 74 69 56 56 56 120), lower := (rows 49 74 69 8 16 32 64), losses := [{ target := 6, region := (rows 127 2 4 127 127 127 0), good := (rows 57 59 61 57 57 57 57) }] }

theorem profile44_node61 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,65] 6 56 profile44_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,65] 6 56 profile44_node61_cert).mp (by decide +kernel))

def profile44_node62_cert : Bound 7 := { allowed := (rows 72 48 48 0 0 0 0), upper := (rows 49 74 76 57 57 57 121), lower := (rows 49 74 76 8 16 32 64), losses := [] }

theorem profile44_node62 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,72] 6 57 profile44_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,72] 6 57 profile44_node62_cert).mp (by decide +kernel))

def profile44_node63_cert : Bound 7 := { allowed := (rows 72 48 40 0 0 0 0), upper := (rows 49 74 84 41 57 41 105), lower := (rows 49 74 84 8 16 32 64), losses := [] }

theorem profile44_node63 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,80] 6 41 profile44_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72,80] 6 41 profile44_node63_cert).mp (by decide +kernel))

def profile44_node54_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile44_node54_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node54 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,72] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile44_node54_route profile44_node54_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node55
  · exact profile44_node58
  · exact profile44_node59
  · exact profile44_node60
  · exact profile44_node61
  · exact profile44_node62
  · exact profile44_node63

def profile44_node64_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 82 109 105 121 105 105), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 65), good := (rows 109 66 4 8 0 32 64) }] }

theorem profile44_node64 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,80] 6 105 profile44_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48,80] 6 105 profile44_node64_cert).mp (by decide +kernel))

def profile44_node38_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile44_node38_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node38 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [48] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile44_node38_route profile44_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile44_node39
  · exact profile44_node46
  · exact profile44_node47
  · exact profile44_node48
  · exact profile44_node49
  · exact profile44_node54
  · exact profile44_node64

def profile44_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile44_node0_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile44_node0 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [] 6 (by decide) (choices 2) [24,48] profile44_node0_route profile44_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile44_node1
  · exact profile44_node38

theorem profile44 : Upper (D (n:=7) [33,32,32,19,18,18,18]) (R (n:=7) [33,32,32,19,18,18,18]) [] 6 := profile44_node0


#print axioms profile44
end Delivery.SmallBudgetTenFinite7
