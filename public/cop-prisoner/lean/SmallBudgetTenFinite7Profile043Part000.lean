import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile43_node2_cert : CutBound 7 := { lost := (rows 16 16 8 0 0 0 0), upper := (rows 11 11 116 120 112 112 112), lower := (rows 11 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 119 119 116 116 116 116 116) },{ target := 4, region := (rows 11 11 4 8 0 32 64), good := (rows 11 11 4 11 0 32 64) }] }

theorem profile43_node2 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,9] 6 112 profile43_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,9] 6 112 profile43_node2_cert).mp (by decide +kernel))

def profile43_node4_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 11 19 28 104 112 96 96), lower := (rows 11 19 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile43_node4 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,24] 6 96 profile43_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,24] 6 96 profile43_node4_cert).mp (by decide +kernel))

def profile43_node6_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 11 19 44 24 112 96 96), lower := (rows 11 19 44 24 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) },{ target := 4, region := (rows 1 2 13 8 0 127 127), good := (rows 111 103 108 108 96 96 96) }] }

theorem profile43_node6 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,16] 6 96 profile43_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,16] 6 96 profile43_node6_cert).mp (by decide +kernel))

def profile43_node7_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 11 19 44 40 80 112 80), lower := (rows 11 19 44 40 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) },{ target := 4, region := (rows 1 2 44 44 0 32 64), good := (rows 15 3 44 44 0 44 64) }] }

theorem profile43_node7 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,32] 6 80 profile43_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,32] 6 80 profile43_node7_cert).mp (by decide +kernel))

def profile43_node9_cert : CutBound 7 := { lost := (rows 32 40 0 0 0 0 0), upper := (rows 11 19 44 72 48 112 80), lower := (rows 11 19 44 72 48 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) },{ target := 5, region := (rows 19 18 4 91 16 0 82), good := (rows 75 91 12 72 91 0 72) }] }

theorem profile43_node9 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,32] 6 80 profile43_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,32] 6 80 profile43_node9_cert).mp (by decide +kernel))

def profile43_node10_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 11 19 44 72 80 48 112), lower := (rows 11 19 44 72 80 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) },{ target := 4, region := (rows 3 2 4 88 0 32 64), good := (rows 11 11 44 72 72 32 72) }] }

theorem profile43_node10 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,64] 6 48 profile43_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64,64] 6 48 profile43_node10_cert).mp (by decide +kernel))

def profile43_node8_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0

def profile43_node8_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node8 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40,64] 6 (by decide) (choices 1) [32,64] profile43_node8_route profile43_node8_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node9
  · exact profile43_node10

def profile43_node5_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node5 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,40] 6 (by decide) (choices 1) [16,32,64] profile43_node5_route profile43_node5_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node6
  · exact profile43_node7
  · exact profile43_node8

def profile43_node12_cert : CutBound 7 := { lost := (rows 48 32 0 0 0 0 0), upper := (rows 11 19 52 40 88 104 72), lower := (rows 11 19 52 40 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) },{ target := 5, region := (rows 9 11 4 8 25 0 73), good := (rows 91 83 20 91 16 0 64) }] }

theorem profile43_node12 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,32] 6 72 profile43_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,32] 6 72 profile43_node12_cert).mp (by decide +kernel))

def profile43_node14_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 11 19 52 72 24 96 96), lower := (rows 11 19 52 72 24 32 64), losses := [{ target := 3, region := (rows 1 2 22 0 16 127 127), good := (rows 103 119 116 96 116 96 96) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile43_node14 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,8] 6 96 profile43_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,8] 6 96 profile43_node14_cert).mp (by decide +kernel))

def profile43_node15_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 11 19 52 72 48 104 72), lower := (rows 11 19 52 72 48 32 64), losses := [{ target := 3, region := (rows 1 2 52 0 52 32 64), good := (rows 3 23 52 64 52 52 64) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile43_node15 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,32] 6 72 profile43_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,32] 6 72 profile43_node15_cert).mp (by decide +kernel))

def profile43_node16_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 11 19 52 72 80 40 104), lower := (rows 11 19 52 72 80 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 88 32 64), good := (rows 19 19 52 80 80 32 80) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile43_node16 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,64] 6 40 profile43_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64,64] 6 40 profile43_node16_cert).mp (by decide +kernel))

def profile43_node13_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node13_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node13 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48,64] 6 (by decide) (choices 1) [8,32,64] profile43_node13_route profile43_node13_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node14
  · exact profile43_node15
  · exact profile43_node16

def profile43_node11_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0

def profile43_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node11 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,48] 6 (by decide) (choices 1) [32,64] profile43_node11_route profile43_node11_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node12
  · exact profile43_node13

def profile43_node18_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 11 19 100 24 120 104 104), lower := (rows 11 19 100 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 15 8 0 41 73), good := (rows 111 103 100 108 0 32 64) },{ target := 5, region := (rows 27 26 4 26 16 0 64), good := (rows 11 27 68 27 27 0 64) }] }

theorem profile43_node18 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,16] 6 104 profile43_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,16] 6 104 profile43_node18_cert).mp (by decide +kernel))

def profile43_node19_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 11 19 100 40 88 120 88), lower := (rows 11 19 100 40 16 32 64), losses := [{ target := 5, region := (rows 9 11 4 8 25 0 73), good := (rows 91 83 68 91 16 0 64) }] }

theorem profile43_node19 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,32] 6 88 profile43_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96,32] 6 88 profile43_node19_cert).mp (by decide +kernel))

def profile43_node17_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node17_route : Route 7 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile43_node17 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17,96] 6 (by decide) (choices 1) [16,32] profile43_node17_route profile43_node17_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node18
  · exact profile43_node19

def profile43_node3_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile43_node3_route : Route 7 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile43_node3 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,17] 6 (by decide) (choices 2) [24,40,48,96] profile43_node3_route profile43_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile43_node4
  · exact profile43_node5
  · exact profile43_node11
  · exact profile43_node17

def profile43_node20_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 11 26 117 121 113 113 113), lower := (rows 11 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 119 18 4 0 16 32 64) },{ target := 4, region := (rows 3 2 4 8 0 32 64), good := (rows 11 11 4 8 0 32 64) }] }

theorem profile43_node20 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,24] 6 113 profile43_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,24] 6 113 profile43_node20_cert).mp (by decide +kernel))

def profile43_node22_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 11 50 13 120 112 112 112), lower := (rows 11 50 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 119 114 114 114 114) },{ target := 4, region := (rows 1 2 5 8 0 32 64), good := (rows 15 34 13 8 0 32 64) }] }

theorem profile43_node22 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,9] 6 112 profile43_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,9] 6 112 profile43_node22_cert).mp (by decide +kernel))

def profile43_node24_cert : CutBound 7 := { lost := (rows 16 0 32 0 0 0 0), upper := (rows 11 50 21 40 88 104 72), lower := (rows 11 50 21 40 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 109 104 104 104 104) },{ target := 5, region := (rows 1 2 5 8 25 0 73), good := (rows 95 18 85 88 16 0 64) }] }

theorem profile43_node24 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,32] 6 72 profile43_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,32] 6 72 profile43_node24_cert).mp (by decide +kernel))

def profile43_node26_cert : CutBound 7 := { lost := (rows 16 8 0 0 0 0 0), upper := (rows 11 50 21 72 24 96 96), lower := (rows 11 50 21 72 24 32 64), losses := [{ target := 3, region := (rows 1 22 4 0 16 127 127), good := (rows 99 114 119 96 114 96 96) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 109 104 104 104 104) }] }

theorem profile43_node26 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,8] 6 96 profile43_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,8] 6 96 profile43_node26_cert).mp (by decide +kernel))

def profile43_node27_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 11 50 21 72 48 104 72), lower := (rows 11 50 21 72 48 32 64), losses := [{ target := 3, region := (rows 1 50 5 0 50 32 64), good := (rows 23 50 23 64 50 50 64) }] }

theorem profile43_node27 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,32] 6 72 profile43_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,32] 6 72 profile43_node27_cert).mp (by decide +kernel))

def profile43_node28_cert : CutBound 7 := { lost := (rows 16 0 8 0 0 0 0), upper := (rows 11 50 21 72 80 40 104), lower := (rows 11 50 21 72 80 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 88 32 64), good := (rows 23 50 21 80 80 32 80) },{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 109 104 104 104 104) }] }

theorem profile43_node28 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,64] 6 40 profile43_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64,64] 6 40 profile43_node28_cert).mp (by decide +kernel))

def profile43_node25_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node25_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node25 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17,64] 6 (by decide) (choices 1) [8,32,64] profile43_node25_route profile43_node25_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node26
  · exact profile43_node27
  · exact profile43_node28

def profile43_node23_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0

def profile43_node23_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node23 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,17] 6 (by decide) (choices 1) [32,64] profile43_node23_route profile43_node23_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node24
  · exact profile43_node25

def profile43_node29_cert : Bound 7 := { allowed := (rows 112 64 96 0 0 0 0), upper := (rows 11 50 28 105 113 97 97), lower := (rows 11 50 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 50 20 0 16 32 64) }] }

theorem profile43_node29 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,24] 6 97 profile43_node29_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,24] 6 97 profile43_node29_cert).mp (by decide +kernel))

def profile43_node30_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 11 50 52 73 89 105 73), lower := (rows 11 50 52 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 64), good := (rows 7 54 54 0 16 32 64) }] }

theorem profile43_node30 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,48] 6 73 profile43_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,48] 6 73 profile43_node30_cert).mp (by decide +kernel))

def profile43_node32_cert : CutBound 7 := { lost := (rows 32 0 16 0 0 0 0), upper := (rows 11 50 69 24 120 104 104), lower := (rows 11 50 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 41 73), good := (rows 111 34 101 104 0 32 64) },{ target := 5, region := (rows 3 2 4 26 16 0 64), good := (rows 11 27 69 24 24 0 64) }] }

theorem profile43_node32 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,16] 6 104 profile43_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,16] 6 104 profile43_node32_cert).mp (by decide +kernel))

def profile43_node33_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 11 50 69 72 56 56 120), lower := (rows 11 50 69 72 16 32 64), losses := [{ target := 6, region := (rows 9 15 4 8 25 41 0), good := (rows 59 50 55 59 16 32 0) }] }

theorem profile43_node33 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,64] 6 56 profile43_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65,64] 6 56 profile43_node33_cert).mp (by decide +kernel))

def profile43_node31_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node31_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile43_node31 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,65] 6 (by decide) (choices 1) [16,64] profile43_node31_route profile43_node31_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node32
  · exact profile43_node33

def profile43_node34_cert : Bound 7 := { allowed := (rows 112 64 48 0 0 0 0), upper := (rows 11 50 76 121 113 113 113), lower := (rows 11 50 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 50 68 0 16 32 64) }] }

theorem profile43_node34 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,72] 6 113 profile43_node34_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,72] 6 113 profile43_node34_cert).mp (by decide +kernel))

def profile43_node35_cert : Bound 7 := { allowed := (rows 96 72 40 0 0 0 0), upper := (rows 11 50 84 105 121 105 105), lower := (rows 11 50 84 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 67), good := (rows 107 107 68 8 0 32 64) }] }

theorem profile43_node35 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,80] 6 105 profile43_node35_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48,80] 6 105 profile43_node35_cert).mp (by decide +kernel))

def profile43_node21_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile43_node21_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile43_node21 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10,48] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile43_node21_route profile43_node21_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile43_node22
  · exact profile43_node23
  · exact profile43_node29
  · exact profile43_node30
  · exact profile43_node31
  · exact profile43_node34
  · exact profile43_node35

def profile43_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile43_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile43_node1 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [10] 6 (by decide) (choices 2) [9,17,24,48] profile43_node1_route profile43_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile43_node2
  · exact profile43_node3
  · exact profile43_node20
  · exact profile43_node21

def profile43_node37_cert : CutBound 7 := { lost := (rows 0 16 8 0 0 0 0), upper := (rows 25 11 118 122 114 114 114), lower := (rows 25 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 66), good := (rows 17 119 4 0 16 32 64) },{ target := 4, region := (rows 1 3 4 8 0 32 64), good := (rows 11 11 4 8 0 32 64) }] }

theorem profile43_node37 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,9] 6 114 profile43_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,9] 6 114 profile43_node37_cert).mp (by decide +kernel))

def profile43_node38_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 25 26 103 107 115 99 99), lower := (rows 25 26 4 8 16 32 64), losses := [{ target := 5, region := (rows 3 3 4 8 16 0 64), good := (rows 27 27 4 8 16 0 64) }] }

theorem profile43_node38 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,24] 6 99 profile43_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,24] 6 99 profile43_node38_cert).mp (by decide +kernel))

def profile43_node41_cert : CutBound 7 := { lost := (rows 0 24 16 0 0 0 0), upper := (rows 25 35 14 24 112 96 96), lower := (rows 25 35 14 24 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 118 112 112 112 112) },{ target := 4, region := (rows 1 3 5 8 0 127 127), good := (rows 111 103 110 104 96 96 96) }] }

theorem profile43_node41 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,16] 6 96 profile43_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,16] 6 96 profile43_node41_cert).mp (by decide +kernel))

def profile43_node42_cert : CutBound 7 := { lost := (rows 0 8 16 0 0 0 0), upper := (rows 25 35 14 40 80 112 80), lower := (rows 25 35 14 40 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 118 112 112 112 112) },{ target := 4, region := (rows 1 2 6 42 0 32 64), good := (rows 9 47 14 40 0 40 64) }] }

theorem profile43_node42 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,32] 6 80 profile43_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,32] 6 80 profile43_node42_cert).mp (by decide +kernel))

def profile43_node44_cert : CutBound 7 := { lost := (rows 32 8 32 0 0 0 0), upper := (rows 25 35 14 72 48 112 80), lower := (rows 25 35 14 72 48 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 118 112 112 112 112) },{ target := 5, region := (rows 17 2 6 91 16 0 81), good := (rows 89 79 14 72 89 0 72) }] }

theorem profile43_node44 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,32] 6 80 profile43_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,32] 6 80 profile43_node44_cert).mp (by decide +kernel))

def profile43_node45_cert : CutBound 7 := { lost := (rows 32 8 0 0 0 0 0), upper := (rows 25 35 14 72 80 48 112), lower := (rows 25 35 14 72 80 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 118 112 112 112 112) },{ target := 5, region := (rows 93 2 4 88 88 0 64), good := (rows 25 3 31 89 89 0 89) }] }

theorem profile43_node45 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,64] 6 48 profile43_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64,64] 6 48 profile43_node45_cert).mp (by decide +kernel))

def profile43_node43_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0

def profile43_node43_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node43 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10,64] 6 (by decide) (choices 1) [32,64] profile43_node43_route profile43_node43_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node44
  · exact profile43_node45

def profile43_node40_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node40_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node40 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,10] 6 (by decide) (choices 1) [16,32,64] profile43_node40_route profile43_node40_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node41
  · exact profile43_node42
  · exact profile43_node43

def profile43_node46_cert : Bound 7 := { allowed := (rows 96 80 96 0 0 0 0), upper := (rows 25 35 28 106 114 98 98), lower := (rows 25 35 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 20 0 16 32 64) }] }

theorem profile43_node46 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,24] 6 98 profile43_node46_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,24] 6 98 profile43_node46_cert).mp (by decide +kernel))

def profile43_node47_cert : CutBound 7 := { lost := (rows 0 0 24 0 0 0 0), upper := (rows 25 35 38 88 88 120 88), lower := (rows 25 35 38 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64), good := (rows 17 39 38 0 16 32 64) },{ target := 4, region := (rows 1 2 6 8 0 32 64), good := (rows 9 39 38 8 0 32 64) }] }

theorem profile43_node47 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,34] 6 88 profile43_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,34] 6 88 profile43_node47_cert).mp (by decide +kernel))

def profile43_node48_cert : Bound 7 := { allowed := (rows 96 80 80 0 0 0 0), upper := (rows 25 35 44 90 82 114 82), lower := (rows 25 35 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 36 0 16 32 64) }] }

theorem profile43_node48 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,40] 6 82 profile43_node48_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,40] 6 82 profile43_node48_cert).mp (by decide +kernel))

def profile43_node50_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 35 70 24 120 104 104), lower := (rows 25 35 70 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 41 73), good := (rows 111 103 70 104 0 32 64) }] }

theorem profile43_node50 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,16] 6 104 profile43_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,16] 6 104 profile43_node50_cert).mp (by decide +kernel))

def profile43_node51_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 25 35 70 40 88 120 88), lower := (rows 25 35 70 40 16 32 64), losses := [{ target := 5, region := (rows 9 2 6 8 25 0 73), good := (rows 89 87 70 89 16 0 64) }] }

theorem profile43_node51 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,32] 6 88 profile43_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,32] 6 88 profile43_node51_cert).mp (by decide +kernel))

def profile43_node52_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 25 35 70 72 56 56 120), lower := (rows 25 35 70 72 16 32 64), losses := [{ target := 6, region := (rows 9 11 4 8 25 41 0), good := (rows 59 51 6 59 16 32 0) }] }

theorem profile43_node52 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,64] 6 56 profile43_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66,64] 6 56 profile43_node52_cert).mp (by decide +kernel))

def profile43_node49_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node49_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node49 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,66] 6 (by decide) (choices 1) [16,32,64] profile43_node49_route profile43_node49_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node50
  · exact profile43_node51
  · exact profile43_node52

def profile43_node53_cert : Bound 7 := { allowed := (rows 96 80 48 0 0 0 0), upper := (rows 25 35 76 122 114 114 114), lower := (rows 25 35 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 68 0 16 32 64) }] }

theorem profile43_node53 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,72] 6 114 profile43_node53_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,72] 6 114 profile43_node53_cert).mp (by decide +kernel))

def profile43_node54_cert : Bound 7 := { allowed := (rows 64 88 24 0 0 0 0), upper := (rows 25 35 100 90 90 122 90), lower := (rows 25 35 100 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 10 18 0 66), good := (rows 25 91 68 8 16 0 64) }] }

theorem profile43_node54 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,96] 6 90 profile43_node54_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33,96] 6 90 profile43_node54_cert).mp (by decide +kernel))

def profile43_node39_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile43_node39_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile43_node39 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,33] 6 (by decide) (choices 2) [10,24,34,40,66,72,96] profile43_node39_route profile43_node39_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile43_node40
  · exact profile43_node46
  · exact profile43_node47
  · exact profile43_node48
  · exact profile43_node49
  · exact profile43_node53
  · exact profile43_node54

def profile43_node57_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 7 24 112 96 96), lower := (rows 25 42 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 11 5 8 0 127 127), good := (rows 111 106 103 106 96 96 96) }] }

theorem profile43_node57 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,16] 6 96 profile43_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,16] 6 96 profile43_node57_cert).mp (by decide +kernel))

def profile43_node58_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 7 40 80 112 80), lower := (rows 25 42 7 40 16 32 64), losses := [{ target := 4, region := (rows 1 42 5 42 0 32 64), good := (rows 15 42 15 42 0 42 64) }] }

theorem profile43_node58 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,32] 6 80 profile43_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,32] 6 80 profile43_node58_cert).mp (by decide +kernel))

def profile43_node60_cert : CutBound 7 := { lost := (rows 96 0 64 0 0 0 0), upper := (rows 25 42 7 72 48 112 80), lower := (rows 25 42 7 72 48 32 64), losses := [{ target := 5, region := (rows 17 2 4 93 16 0 81), good := (rows 89 10 79 72 89 0 72) },{ target := 6, region := (rows 3 2 6 8 50 32 0), good := (rows 25 63 23 8 48 48 0) }] }

theorem profile43_node60 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,32] 6 80 profile43_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,32] 6 80 profile43_node60_cert).mp (by decide +kernel))

def profile43_node61_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 25 42 7 72 80 48 112), lower := (rows 25 42 7 72 80 32 64), losses := [{ target := 5, region := (rows 91 2 6 88 88 0 64), good := (rows 25 31 7 89 89 0 89) }] }

theorem profile43_node61 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,64] 6 48 profile43_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64,64] 6 48 profile43_node61_cert).mp (by decide +kernel))

def profile43_node59_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0

def profile43_node59_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node59 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3,64] 6 (by decide) (choices 1) [32,64] profile43_node59_route profile43_node59_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node60
  · exact profile43_node61

def profile43_node56_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node56_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node56 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,3] 6 (by decide) (choices 1) [16,32,64] profile43_node56_route profile43_node56_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node57
  · exact profile43_node58
  · exact profile43_node59

def profile43_node62_cert : Bound 7 := { allowed := (rows 96 80 96 0 0 0 0), upper := (rows 25 42 21 106 114 98 98), lower := (rows 25 42 21 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 18 34 66), good := (rows 21 114 21 0 16 32 64) }] }

theorem profile43_node62 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,17] 6 98 profile43_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,17] 6 98 profile43_node62_cert).mp (by decide +kernel))

def profile43_node63_cert : Bound 7 := { allowed := (rows 96 64 104 0 0 0 0), upper := (rows 25 42 22 105 113 97 97), lower := (rows 25 42 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 9 0 33 65), good := (rows 107 42 6 8 0 32 64) }] }

theorem profile43_node63 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,18] 6 97 profile43_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,18] 6 97 profile43_node63_cert).mp (by decide +kernel))

def profile43_node64_cert : Bound 7 := { allowed := (rows 64 80 88 0 0 0 0), upper := (rows 25 42 37 90 82 114 82), lower := (rows 25 42 37 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 10 18 0 66), good := (rows 25 91 5 8 16 0 64) }] }

theorem profile43_node64 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,33] 6 82 profile43_node64_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,33] 6 82 profile43_node64_cert).mp (by decide +kernel))

def profile43_node65_cert : Bound 7 := { allowed := (rows 96 80 80 0 0 0 0), upper := (rows 25 42 38 89 81 113 81), lower := (rows 25 42 38 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 17 33 65), good := (rows 113 38 38 0 16 32 64) }] }

theorem profile43_node65 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,34] 6 81 profile43_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,34] 6 81 profile43_node65_cert).mp (by decide +kernel))

def profile43_node66_cert : Bound 7 := { allowed := (rows 96 80 72 0 0 0 0), upper := (rows 25 42 52 75 83 99 67), lower := (rows 25 42 52 8 16 32 64), losses := [] }

theorem profile43_node66 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,48] 6 67 profile43_node66_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,48] 6 67 profile43_node66_cert).mp (by decide +kernel))

def profile43_node68_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 42 69 10 112 112 112), lower := (rows 25 42 69 10 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 127 127 127), good := (rows 117 114 117 114 112 112 112) }] }

theorem profile43_node68 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,2] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,2] 6 112 profile43_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,2] 6 112 profile43_node68_cert).mp (by decide +kernel))

def profile43_node69_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 69 24 114 98 98), lower := (rows 25 42 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 11 5 8 0 47 79), good := (rows 111 106 103 106 0 32 64) }] }

theorem profile43_node69 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,16] 6 98 profile43_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,16] 6 98 profile43_node69_cert).mp (by decide +kernel))

def profile43_node70_cert : Bound 7 := { allowed := (rows 96 64 56 0 0 0 0), upper := (rows 25 42 69 40 82 114 82), lower := (rows 25 42 69 40 16 32 64), losses := [{ target := 4, region := (rows 1 42 4 42 0 32 64), good := (rows 11 42 69 42 0 42 64) }] }

theorem profile43_node70 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,32] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,32] 6 82 profile43_node70_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,32] 6 82 profile43_node70_cert).mp (by decide +kernel))

def profile43_node71_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 25 42 69 72 50 50 114), lower := (rows 25 42 69 72 16 32 64), losses := [{ target := 6, region := (rows 11 11 4 8 31 47 0), good := (rows 59 59 55 59 16 32 0) }] }

theorem profile43_node71 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,64] 6 50 profile43_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65,64] 6 50 profile43_node71_cert).mp (by decide +kernel))

def profile43_node67_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 4 => 2 | _ => 0

def profile43_node67_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node67 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,65] 6 (by decide) (choices 1) [2,16,32,64] profile43_node67_route profile43_node67_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile43_node68
  · exact profile43_node69
  · exact profile43_node70
  · exact profile43_node71

def profile43_node73_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 42 70 9 112 112 112), lower := (rows 25 42 70 9 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 127 127 127), good := (rows 113 118 118 113 112 112 112) }] }

theorem profile43_node73 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,1] 6 112 profile43_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,1] 6 112 profile43_node73_cert).mp (by decide +kernel))

def profile43_node74_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 70 24 113 97 97), lower := (rows 25 42 70 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 33 65), good := (rows 111 42 70 8 0 32 64) }] }

theorem profile43_node74 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,16] 6 97 profile43_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,16] 6 97 profile43_node74_cert).mp (by decide +kernel))

def profile43_node75_cert : Bound 7 := { allowed := (rows 96 64 56 0 0 0 0), upper := (rows 25 42 70 40 81 113 81), lower := (rows 25 42 70 40 16 32 64), losses := [{ target := 4, region := (rows 1 42 4 42 0 32 64), good := (rows 11 42 78 42 0 42 64) }] }

theorem profile43_node75 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,32] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,32] 6 81 profile43_node75_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,32] 6 81 profile43_node75_cert).mp (by decide +kernel))

def profile43_node76_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 25 42 70 72 49 49 113), lower := (rows 25 42 70 72 16 32 64), losses := [{ target := 6, region := (rows 11 11 4 8 31 47 0), good := (rows 59 59 55 59 16 32 0) }] }

theorem profile43_node76 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,64] 6 49 profile43_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66,64] 6 49 profile43_node76_cert).mp (by decide +kernel))

def profile43_node72_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0

def profile43_node72_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node72 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,66] 6 (by decide) (choices 1) [1,16,32,64] profile43_node72_route profile43_node72_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile43_node73
  · exact profile43_node74
  · exact profile43_node75
  · exact profile43_node76

def profile43_node77_cert : Bound 7 := { allowed := (rows 96 80 40 0 0 0 0), upper := (rows 25 42 84 107 115 99 99), lower := (rows 25 42 84 8 16 32 64), losses := [] }

theorem profile43_node77 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,80] 6 99 profile43_node77_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,80] 6 99 profile43_node77_cert).mp (by decide +kernel))

def profile43_node78_cert : Bound 7 := { allowed := (rows 96 80 24 0 0 0 0), upper := (rows 25 42 100 91 83 115 83), lower := (rows 25 42 100 8 16 32 64), losses := [] }

theorem profile43_node78 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,96] 6 83 profile43_node78_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40,96] 6 83 profile43_node78_cert).mp (by decide +kernel))

def profile43_node55_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile43_node55_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node55 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,40] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile43_node55_route profile43_node55_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile43_node56
  · exact profile43_node62
  · exact profile43_node63
  · exact profile43_node64
  · exact profile43_node65
  · exact profile43_node66
  · exact profile43_node67
  · exact profile43_node72
  · exact profile43_node77
  · exact profile43_node78

def profile43_node81_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 98 7 24 120 104 104), lower := (rows 25 98 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 15 5 8 0 41 73), good := (rows 111 98 103 106 0 32 64) }] }

theorem profile43_node81 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,16] 6 104 profile43_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,16] 6 104 profile43_node81_cert).mp (by decide +kernel))

def profile43_node83_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 25 98 7 40 24 112 80), lower := (rows 25 98 7 40 24 32 64), losses := [{ target := 3, region := (rows 1 23 5 0 16 49 81), good := (rows 119 98 103 32 114 32 64) }] }

theorem profile43_node83 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,8] 6 80 profile43_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,8] 6 80 profile43_node83_cert).mp (by decide +kernel))

def profile43_node84_cert : CutBound 7 := { lost := (rows 96 0 0 0 0 0 0), upper := (rows 25 98 7 40 80 56 88), lower := (rows 25 98 7 40 80 32 64), losses := [{ target := 5, region := (rows 9 2 4 8 95 0 73), good := (rows 89 82 87 89 80 0 80) },{ target := 6, region := (rows 17 2 4 63 16 49 0), good := (rows 57 42 47 40 57 40 0) }] }

theorem profile43_node84 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,64] 6 24 profile43_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32,64] 6 24 profile43_node84_cert).mp (by decide +kernel))

def profile43_node82_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0

def profile43_node82_route : Route 7 := (fun mask => (mask,id))

theorem profile43_node82 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3,32] 6 (by decide) (choices 1) [8,64] profile43_node82_route profile43_node82_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node83
  · exact profile43_node84

def profile43_node80_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile43_node80_route : Route 7 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile43_node80 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,3] 6 (by decide) (choices 1) [16,32] profile43_node80_route profile43_node80_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node81
  · exact profile43_node82

def profile43_node85_cert : Bound 7 := { allowed := (rows 96 16 112 0 0 0 0), upper := (rows 25 98 13 122 114 114 114), lower := (rows 25 98 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 119 114 114 114 114) }] }

theorem profile43_node85 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,9] 6 114 profile43_node85_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,9] 6 114 profile43_node85_cert).mp (by decide +kernel))

def profile43_node86_cert : Bound 7 := { allowed := (rows 96 16 112 0 0 0 0), upper := (rows 25 98 14 121 113 113 113), lower := (rows 25 98 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 98 6 0 16 32 64) }] }

theorem profile43_node86 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,10] 6 113 profile43_node86_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,10] 6 113 profile43_node86_cert).mp (by decide +kernel))

def profile43_node87_cert : Bound 7 := { allowed := (rows 96 24 96 0 0 0 0), upper := (rows 25 98 28 107 115 99 99), lower := (rows 25 98 28 8 16 32 64), losses := [] }

theorem profile43_node87 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,24] 6 99 profile43_node87_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,24] 6 99 profile43_node87_cert).mp (by decide +kernel))

def profile43_node88_cert : Bound 7 := { allowed := (rows 64 24 88 0 0 0 0), upper := (rows 25 98 37 90 90 122 90), lower := (rows 25 98 37 8 16 32 64), losses := [{ target := 5, region := (rows 3 2 4 10 18 0 66), good := (rows 25 91 5 8 16 0 64) }] }

theorem profile43_node88 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,33] 6 90 profile43_node88_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,33] 6 90 profile43_node88_cert).mp (by decide +kernel))

def profile43_node89_cert : Bound 7 := { allowed := (rows 96 24 80 0 0 0 0), upper := (rows 25 98 38 89 89 121 89), lower := (rows 25 98 38 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64), good := (rows 17 102 38 0 16 32 64) }] }

theorem profile43_node89 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,34] 6 89 profile43_node89_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,34] 6 89 profile43_node89_cert).mp (by decide +kernel))

def profile43_node90_cert : Bound 7 := { allowed := (rows 96 24 80 0 0 0 0), upper := (rows 25 98 44 91 83 115 83), lower := (rows 25 98 44 8 16 32 64), losses := [] }

theorem profile43_node90 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,40] 6 83 profile43_node90_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,40] 6 83 profile43_node90_cert).mp (by decide +kernel))

def profile43_node91_cert : Bound 7 := { allowed := (rows 96 24 24 0 0 0 0), upper := (rows 25 98 100 27 27 59 91), lower := (rows 25 98 100 8 16 32 64), losses := [] }

theorem profile43_node91 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,96] 6 27 profile43_node91_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96,96] 6 27 profile43_node91_cert).mp (by decide +kernel))

def profile43_node79_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile43_node79_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile43_node79 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24,96] 6 (by decide) (choices 2) [3,9,10,24,33,34,40,96] profile43_node79_route profile43_node79_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile43_node80
  · exact profile43_node85
  · exact profile43_node86
  · exact profile43_node87
  · exact profile43_node88
  · exact profile43_node89
  · exact profile43_node90
  · exact profile43_node91

def profile43_node36_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile43_node36_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile43_node36 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [24] 6 (by decide) (choices 2) [9,24,33,40,96] profile43_node36_route profile43_node36_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile43_node37
  · exact profile43_node38
  · exact profile43_node39
  · exact profile43_node55
  · exact profile43_node79

def profile43_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile43_node0_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 34 => (10,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 66 => (10,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (24,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 96 => (24,(fun i => match i.val with | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile43_node0 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [] 6 (by decide) (choices 2) [10,24] profile43_node0_route profile43_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile43_node1
  · exact profile43_node36

theorem profile43 : Upper (D (n:=7) [33,33,32,18,18,18,18]) (R (n:=7) [33,33,32,18,18,18,18]) [] 6 := profile43_node0


#print axioms profile43
end Delivery.SmallBudgetTenFinite7
