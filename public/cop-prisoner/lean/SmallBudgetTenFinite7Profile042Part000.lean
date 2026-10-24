import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile42_node2_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 11 117 121 113 113 113), lower := (rows 25 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 67), good := (rows 117 119 4 0 16 32 64) },{ target := 4, region := (rows 1 3 4 8 0 32 64), good := (rows 11 11 4 8 0 32 64) }] }

theorem profile42_node2 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,9] 6 113 profile42_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,9] 6 113 profile42_node2_cert).mp (by decide +kernel))

def profile42_node3_cert : CutBound 7 := { lost := (rows 0 1 8 0 0 0 0), upper := (rows 25 26 101 105 113 97 97), lower := (rows 25 26 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 64), good := (rows 26 26 4 8 16 32 64) },{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 18 4 0 16 32 64) }] }

theorem profile42_node3 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,24] 6 97 profile42_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,24] 6 97 profile42_node3_cert).mp (by decide +kernel))

def profile42_node5_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 25 35 13 120 112 112 112), lower := (rows 25 35 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 7 4 0 127 127 127), good := (rows 115 115 119 112 112 112 112) },{ target := 4, region := (rows 1 2 5 8 0 32 64), good := (rows 13 39 13 8 0 32 64) }] }

theorem profile42_node5 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,9] 6 112 profile42_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,9] 6 112 profile42_node5_cert).mp (by decide +kernel))

def profile42_node6_cert : CutBound 7 := { lost := (rows 0 8 1 0 0 0 0), upper := (rows 25 35 28 105 113 97 97), lower := (rows 25 35 28 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 64), good := (rows 28 38 28 8 16 32 64) },{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 20 0 16 32 64) }] }

theorem profile42_node6 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,24] 6 97 profile42_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,24] 6 97 profile42_node6_cert).mp (by decide +kernel))

def profile42_node7_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 25 35 37 88 88 120 88), lower := (rows 25 35 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64), good := (rows 17 39 39 0 16 32 64) }] }

theorem profile42_node7 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,33] 6 88 profile42_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,33] 6 88 profile42_node7_cert).mp (by decide +kernel))

def profile42_node8_cert : CutBound 7 := { lost := (rows 32 8 0 0 0 0 0), upper := (rows 25 35 44 89 81 113 81), lower := (rows 25 35 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 36 0 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node8 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,40] 6 81 profile42_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,40] 6 81 profile42_node8_cert).mp (by decide +kernel))

def profile42_node10_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 35 69 24 120 104 104), lower := (rows 25 35 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 7 7 8 0 41 73), good := (rows 111 103 103 104 0 32 64) }] }

theorem profile42_node10 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,16] 6 104 profile42_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,16] 6 104 profile42_node10_cert).mp (by decide +kernel))

def profile42_node11_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 25 35 69 40 88 120 88), lower := (rows 25 35 69 40 16 32 64), losses := [{ target := 5, region := (rows 9 2 15 8 25 0 73), good := (rows 93 87 85 93 16 0 64) }] }

theorem profile42_node11 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,32] 6 88 profile42_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,32] 6 88 profile42_node11_cert).mp (by decide +kernel))

def profile42_node12_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 25 35 69 72 56 56 120), lower := (rows 25 35 69 72 16 32 64), losses := [{ target := 6, region := (rows 9 15 4 8 25 41 0), good := (rows 59 51 55 59 16 32 0) }] }

theorem profile42_node12 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,64] 6 56 profile42_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65,64] 6 56 profile42_node12_cert).mp (by decide +kernel))

def profile42_node9_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile42_node9_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node9 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,65] 6 (by decide) (choices 1) [16,32,64] profile42_node9_route profile42_node9_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node10
  · exact profile42_node11
  · exact profile42_node12

def profile42_node14_cert : CutBound 7 := { lost := (rows 0 8 1 0 0 0 0), upper := (rows 25 35 76 9 112 112 112), lower := (rows 25 35 76 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 13 8 127 127 127), good := (rows 124 118 124 124 112 112 112) },{ target := 3, region := (rows 1 11 4 0 127 127 127), good := (rows 115 115 118 115 112 112 112) }] }

theorem profile42_node14 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,1] 6 112 profile42_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,1] 6 112 profile42_node14_cert).mp (by decide +kernel))

def profile42_node15_cert : CutBound 7 := { lost := (rows 0 24 16 0 0 0 0), upper := (rows 25 35 76 24 113 97 97), lower := (rows 25 35 76 24 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 68 16 16 32 64) },{ target := 4, region := (rows 1 3 5 8 0 35 67), good := (rows 111 103 76 8 0 32 64) }] }

theorem profile42_node15 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,16] 6 97 profile42_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,16] 6 97 profile42_node15_cert).mp (by decide +kernel))

def profile42_node16_cert : CutBound 7 := { lost := (rows 32 8 32 0 0 0 0), upper := (rows 25 35 76 40 81 113 81), lower := (rows 25 35 76 40 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 68 32 16 32 64) },{ target := 5, region := (rows 13 2 13 8 31 0 79), good := (rows 93 87 93 93 16 0 64) }] }

theorem profile42_node16 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,32] 6 81 profile42_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,32] 6 81 profile42_node16_cert).mp (by decide +kernel))

def profile42_node17_cert : CutBound 7 := { lost := (rows 0 8 1 0 0 0 0), upper := (rows 25 35 76 72 49 49 113), lower := (rows 25 35 76 72 16 32 64), losses := [{ target := 0, region := (rows 0 2 76 76 16 32 64), good := (rows 28 34 76 76 16 32 76) },{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 68 64 16 32 64) }] }

theorem profile42_node17 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,64] 6 49 profile42_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72,64] 6 49 profile42_node17_cert).mp (by decide +kernel))

def profile42_node13_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0

def profile42_node13_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node13 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,72] 6 (by decide) (choices 1) [1,16,32,64] profile42_node13_route profile42_node13_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile42_node14
  · exact profile42_node15
  · exact profile42_node16
  · exact profile42_node17

def profile42_node19_cert : CutBound 7 := { lost := (rows 32 0 1 0 0 0 0), upper := (rows 25 35 100 9 88 120 88), lower := (rows 25 35 100 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 25 41 73), good := (rows 124 118 100 124 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node19 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,1] 6 88 profile42_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,1] 6 88 profile42_node19_cert).mp (by decide +kernel))

def profile42_node20_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 35 100 24 89 105 73), lower := (rows 25 35 100 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 33 65), good := (rows 111 103 100 8 0 32 64) }] }

theorem profile42_node20 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,16] 6 73 profile42_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,16] 6 73 profile42_node20_cert).mp (by decide +kernel))

def profile42_node21_cert : CutBound 7 := { lost := (rows 96 64 0 0 0 0 0), upper := (rows 25 35 100 72 25 57 89), lower := (rows 25 35 100 72 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) },{ target := 6, region := (rows 9 11 4 8 25 41 0), good := (rows 59 51 36 59 16 32 0) }] }

theorem profile42_node21 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,64] 6 25 profile42_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96,64] 6 25 profile42_node21_cert).mp (by decide +kernel))

def profile42_node18_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0

def profile42_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node18 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33,96] 6 (by decide) (choices 1) [1,16,64] profile42_node18_route profile42_node18_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node19
  · exact profile42_node20
  · exact profile42_node21

def profile42_node4_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile42_node4_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile42_node4 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,33] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile42_node4_route profile42_node4_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile42_node5
  · exact profile42_node6
  · exact profile42_node7
  · exact profile42_node8
  · exact profile42_node9
  · exact profile42_node13
  · exact profile42_node18

def profile42_node23_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 42 21 105 113 97 97), lower := (rows 25 42 21 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 21 37 69), good := (rows 117 34 117 0 16 32 64) },{ target := 4, region := (rows 1 7 4 13 0 37 69), good := (rows 107 42 111 8 0 32 64) }] }

theorem profile42_node23 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,17] 6 97 profile42_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,17] 6 97 profile42_node23_cert).mp (by decide +kernel))

def profile42_node24_cert : CutBound 7 := { lost := (rows 32 0 8 0 0 0 0), upper := (rows 25 42 37 89 81 113 81), lower := (rows 25 42 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 21 37 69), good := (rows 117 34 117 0 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node24 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,33] 6 81 profile42_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,33] 6 81 profile42_node24_cert).mp (by decide +kernel))

def profile42_node25_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 42 52 73 81 97 65), lower := (rows 25 42 52 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 34 52 0 16 32 64) },{ target := 4, region := (rows 1 3 4 9 0 33 65), good := (rows 107 42 36 8 0 32 64) }] }

theorem profile42_node25 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,48] 6 65 profile42_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,48] 6 65 profile42_node25_cert).mp (by decide +kernel))

def profile42_node27_cert : CutBound 7 := { lost := (rows 0 1 8 0 0 0 0), upper := (rows 25 42 69 9 112 112 112), lower := (rows 25 42 69 9 16 32 64), losses := [{ target := 0, region := (rows 0 11 4 8 127 127 127), good := (rows 122 122 118 122 112 112 112) },{ target := 3, region := (rows 1 2 13 0 127 127 127), good := (rows 117 118 117 117 112 112 112) }] }

theorem profile42_node27 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,1] 6 112 profile42_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,1] 6 112 profile42_node27_cert).mp (by decide +kernel))

def profile42_node28_cert : CutBound 7 := { lost := (rows 0 16 24 0 0 0 0), upper := (rows 25 42 69 24 113 97 97), lower := (rows 25 42 69 24 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 21 37 69), good := (rows 117 34 117 16 16 32 64) },{ target := 4, region := (rows 1 3 5 8 0 37 69), good := (rows 111 42 103 8 0 32 64) }] }

theorem profile42_node28 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,16] 6 97 profile42_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,16] 6 97 profile42_node28_cert).mp (by decide +kernel))

def profile42_node29_cert : CutBound 7 := { lost := (rows 0 1 8 0 0 0 0), upper := (rows 25 42 69 40 81 113 81), lower := (rows 25 42 69 40 16 32 64), losses := [{ target := 0, region := (rows 0 42 4 42 16 32 64), good := (rows 26 42 68 42 16 42 64) },{ target := 3, region := (rows 1 2 5 0 21 37 69), good := (rows 117 34 117 32 16 32 64) }] }

theorem profile42_node29 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,32] 6 81 profile42_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,32] 6 81 profile42_node29_cert).mp (by decide +kernel))

def profile42_node30_cert : CutBound 7 := { lost := (rows 64 64 8 0 0 0 0), upper := (rows 25 42 69 72 49 49 113), lower := (rows 25 42 69 72 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 21 37 69), good := (rows 117 34 117 64 16 32 64) },{ target := 6, region := (rows 11 11 4 8 31 47 0), good := (rows 59 59 55 59 16 32 0) }] }

theorem profile42_node30 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,64] 6 49 profile42_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65,64] 6 49 profile42_node30_cert).mp (by decide +kernel))

def profile42_node26_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0

def profile42_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node26 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,65] 6 (by decide) (choices 1) [1,16,32,64] profile42_node26_route profile42_node26_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile42_node27
  · exact profile42_node28
  · exact profile42_node29
  · exact profile42_node30

def profile42_node31_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 42 84 105 113 97 97), lower := (rows 25 42 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 34 84 0 16 32 64) },{ target := 4, region := (rows 1 3 4 9 0 33 65), good := (rows 107 42 68 8 0 32 64) }] }

theorem profile42_node31 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,80] 6 97 profile42_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,80] 6 97 profile42_node31_cert).mp (by decide +kernel))

def profile42_node32_cert : CutBound 7 := { lost := (rows 32 0 8 0 0 0 0), upper := (rows 25 42 100 89 81 113 81), lower := (rows 25 42 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 117 34 100 0 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node32 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,96] 6 81 profile42_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40,96] 6 81 profile42_node32_cert).mp (by decide +kernel))

def profile42_node22_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile42_node22_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node22 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,40] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile42_node22_route profile42_node22_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile42_node23
  · exact profile42_node24
  · exact profile42_node25
  · exact profile42_node26
  · exact profile42_node31
  · exact profile42_node32

def profile42_node34_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 25 98 13 121 113 113 113), lower := (rows 25 98 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 7 4 0 21 37 69), good := (rows 115 98 119 0 16 32 64) },{ target := 4, region := (rows 1 2 5 8 0 32 64), good := (rows 13 98 13 8 0 32 64) }] }

theorem profile42_node34 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,9] 6 113 profile42_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,9] 6 113 profile42_node34_cert).mp (by decide +kernel))

def profile42_node35_cert : CutBound 7 := { lost := (rows 0 8 1 0 0 0 0), upper := (rows 25 98 28 105 113 97 97), lower := (rows 25 98 28 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 64), good := (rows 28 98 28 8 16 32 64) },{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 98 20 0 16 32 64) }] }

theorem profile42_node35 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,24] 6 97 profile42_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,24] 6 97 profile42_node35_cert).mp (by decide +kernel))

def profile42_node37_cert : CutBound 7 := { lost := (rows 32 1 0 0 0 0 0), upper := (rows 25 98 37 9 88 120 88), lower := (rows 25 98 37 9 16 32 64), losses := [{ target := 0, region := (rows 0 15 4 8 25 41 73), good := (rows 122 98 118 122 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node37 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,1] 6 88 profile42_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,1] 6 88 profile42_node37_cert).mp (by decide +kernel))

def profile42_node38_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 98 37 24 89 105 73), lower := (rows 25 98 37 24 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 8 0 33 65), good := (rows 111 98 103 8 0 32 64) }] }

theorem profile42_node38 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,16] 6 73 profile42_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,16] 6 73 profile42_node38_cert).mp (by decide +kernel))

def profile42_node39_cert : CutBound 7 := { lost := (rows 96 0 64 0 0 0 0), upper := (rows 25 98 37 72 25 57 89), lower := (rows 25 98 37 72 16 32 64), losses := [{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) },{ target := 6, region := (rows 9 2 13 8 25 41 0), good := (rows 61 34 53 61 16 32 0) }] }

theorem profile42_node39 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,64] 6 25 profile42_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33,64] 6 25 profile42_node39_cert).mp (by decide +kernel))

def profile42_node36_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0

def profile42_node36_route : Route 7 := (fun mask => (mask,id))

theorem profile42_node36 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,33] 6 (by decide) (choices 1) [1,16,64] profile42_node36_route profile42_node36_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node37
  · exact profile42_node38
  · exact profile42_node39

def profile42_node40_cert : CutBound 7 := { lost := (rows 32 8 0 0 0 0 0), upper := (rows 25 98 44 89 81 113 81), lower := (rows 25 98 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 98 36 0 16 32 64) },{ target := 5, region := (rows 127 2 4 127 127 0 127), good := (rows 89 91 93 89 89 89 89) }] }

theorem profile42_node40 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,40] 6 81 profile42_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,40] 6 81 profile42_node40_cert).mp (by decide +kernel))

def profile42_node41_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 25 98 100 25 25 57 89), lower := (rows 25 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 64), good := (rows 24 102 102 8 16 32 64) }] }

theorem profile42_node41 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,96] 6 25 profile42_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96,96] 6 25 profile42_node41_cert).mp (by decide +kernel))

def profile42_node33_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile42_node33_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile42_node33 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24,96] 6 (by decide) (choices 2) [9,24,33,40,96] profile42_node33_route profile42_node33_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile42_node34
  · exact profile42_node35
  · exact profile42_node36
  · exact profile42_node40
  · exact profile42_node41

def profile42_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile42_node1_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile42_node1 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [24] 6 (by decide) (choices 2) [9,24,33,40,96] profile42_node1_route profile42_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile42_node2
  · exact profile42_node3
  · exact profile42_node4
  · exact profile42_node22
  · exact profile42_node33

def profile42_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile42_node0_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (24,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 96 => (24,(fun i => match i.val with | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile42_node0 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [] 6 (by decide) (choices 2) [24] profile42_node0_route profile42_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=7) [34,32,32,18,18,18,18]) (R (n:=7) [34,32,32,18,18,18,18]) [] 6 := profile42_node0


#print axioms profile42
end Delivery.SmallBudgetTenFinite7
