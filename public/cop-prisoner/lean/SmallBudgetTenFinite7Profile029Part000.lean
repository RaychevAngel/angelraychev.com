import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile29_node2_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 27 11 116 120 112 112 64), lower := (rows 27 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 119 119 116 116 116 116 116) }] }

theorem profile29_node2 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,9] 6 112 profile29_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,9] 6 112 profile29_node2_cert).mp (by decide +kernel))

def profile29_node3_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 27 26 101 105 113 97 64), lower := (rows 27 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 119 82 68 64 80 96 64) }] }

theorem profile29_node3 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,24] 6 97 profile29_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,24] 6 97 profile29_node3_cert).mp (by decide +kernel))

def profile29_node5_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 27 35 28 104 112 96 64), lower := (rows 27 35 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node5 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,24] 6 96 profile29_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,24] 6 96 profile29_node5_cert).mp (by decide +kernel))

def profile29_node6_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 27 35 44 88 80 112 64), lower := (rows 27 35 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node6 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,40] 6 80 profile29_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,40] 6 80 profile29_node6_cert).mp (by decide +kernel))

def profile29_node7_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 27 35 76 120 112 112 64), lower := (rows 27 35 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node7 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,72] 6 112 profile29_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,72] 6 112 profile29_node7_cert).mp (by decide +kernel))

def profile29_node8_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 27 35 100 88 88 120 64), lower := (rows 27 35 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 38 0 16 32 127), good := (rows 87 103 100 64 80 100 64) }] }

theorem profile29_node8 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,96] 6 88 profile29_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33,96] 6 88 profile29_node8_cert).mp (by decide +kernel))

def profile29_node4_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile29_node4_route : Route 7 := (fun mask => match mask with | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node4 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,33] 6 (by decide) (choices 2) [24,40,72,96] profile29_node4_route profile29_node4_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node5
  · exact profile29_node6
  · exact profile29_node7
  · exact profile29_node8

def profile29_node9_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 27 42 117 121 113 113 64), lower := (rows 27 42 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 119 98 68 64 80 96 64) }] }

theorem profile29_node9 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,40] 6 113 profile29_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,40] 6 113 profile29_node9_cert).mp (by decide +kernel))

def profile29_node10_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 27 67 124 120 120 120 64), lower := (rows 27 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 83 67 68 64 80 96 64) }] }

theorem profile29_node10 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,65] 6 120 profile29_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,65] 6 120 profile29_node10_cert).mp (by decide +kernel))

def profile29_node11_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 27 74 117 121 113 113 64), lower := (rows 27 74 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 119 66 68 64 80 96 64) }] }

theorem profile29_node11 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,72] 6 113 profile29_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,72] 6 113 profile29_node11_cert).mp (by decide +kernel))

def profile29_node12_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 27 98 125 121 121 121 64), lower := (rows 27 98 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 127), good := (rows 83 98 68 64 80 98 64) }] }

theorem profile29_node12 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,96] 6 121 profile29_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26,96] 6 121 profile29_node12_cert).mp (by decide +kernel))

def profile29_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile29_node1_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node1 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [26] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile29_node1_route profile29_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node2
  · exact profile29_node3
  · exact profile29_node4
  · exact profile29_node9
  · exact profile29_node10
  · exact profile29_node11
  · exact profile29_node12

def profile29_node14_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 57 11 118 122 114 114 64), lower := (rows 57 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 127), good := (rows 113 119 68 64 80 96 64) }] }

theorem profile29_node14 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,9] 6 114 profile29_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,9] 6 114 profile29_node14_cert).mp (by decide +kernel))

def profile29_node15_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 57 26 103 107 115 99 64), lower := (rows 57 26 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 91 90 68 72 80 64 64) }] }

theorem profile29_node15 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,24] 6 99 profile29_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,24] 6 99 profile29_node15_cert).mp (by decide +kernel))

def profile29_node16_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 57 67 126 122 122 122 64), lower := (rows 57 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 115 67 68 64 80 96 64) }] }

theorem profile29_node16 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,65] 6 122 profile29_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,65] 6 122 profile29_node16_cert).mp (by decide +kernel))

def profile29_node17_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 57 74 119 123 115 115 64), lower := (rows 57 74 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 11 4 8 0 32 127), good := (rows 107 74 68 74 64 96 64) }] }

theorem profile29_node17 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,72] 6 115 profile29_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56,72] 6 115 profile29_node17_cert).mp (by decide +kernel))

def profile29_node13_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile29_node13_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node13 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [56] 6 (by decide) (choices 2) [9,24,65,72] profile29_node13_route profile29_node13_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node14
  · exact profile29_node15
  · exact profile29_node16
  · exact profile29_node17

def profile29_node19_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 11 116 120 112 112 64), lower := (rows 75 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 127 0 127 127 127), good := (rows 119 119 116 116 116 116 116) }] }

theorem profile29_node19 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,9] 6 112 profile29_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,9] 6 112 profile29_node19_cert).mp (by decide +kernel))

def profile29_node21_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 19 28 104 112 96 64), lower := (rows 75 19 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node21 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,24] 6 96 profile29_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,24] 6 96 profile29_node21_cert).mp (by decide +kernel))

def profile29_node22_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 19 44 120 112 112 64), lower := (rows 75 19 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node22 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,40] 6 112 profile29_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,40] 6 112 profile29_node22_cert).mp (by decide +kernel))

def profile29_node23_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 75 19 52 104 120 104 64), lower := (rows 75 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 108 104 104 104 104) }] }

theorem profile29_node23 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,48] 6 104 profile29_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,48] 6 104 profile29_node23_cert).mp (by decide +kernel))

def profile29_node24_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 19 76 56 48 48 64), lower := (rows 75 19 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 116 112 112 112 112) }] }

theorem profile29_node24 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,72] 6 48 profile29_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,72] 6 48 profile29_node24_cert).mp (by decide +kernel))

def profile29_node25_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 19 84 40 56 40 64), lower := (rows 75 19 84 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 127), good := (rows 71 87 84 64 84 96 64) }] }

theorem profile29_node25 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,80] 6 40 profile29_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,80] 6 40 profile29_node25_cert).mp (by decide +kernel))

def profile29_node26_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 19 100 56 56 56 64), lower := (rows 75 19 100 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 36 0 16 32 127), good := (rows 67 83 100 64 80 100 64) }] }

theorem profile29_node26 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,96] 6 56 profile29_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17,96] 6 56 profile29_node26_cert).mp (by decide +kernel))

def profile29_node20_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile29_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile29_node20 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,17] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile29_node20_route profile29_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node21
  · exact profile29_node22
  · exact profile29_node23
  · exact profile29_node24
  · exact profile29_node25
  · exact profile29_node26

def profile29_node27_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 26 117 121 113 113 64), lower := (rows 75 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 119 82 68 64 80 96 64) }] }

theorem profile29_node27 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,24] 6 113 profile29_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,24] 6 113 profile29_node27_cert).mp (by decide +kernel))

def profile29_node29_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 50 13 120 112 112 64), lower := (rows 75 50 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 127 4 0 127 127 127), good := (rows 115 114 119 114 114 114 114) }] }

theorem profile29_node29 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,9] 6 112 profile29_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,9] 6 112 profile29_node29_cert).mp (by decide +kernel))

def profile29_node30_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 75 50 21 104 120 104 64), lower := (rows 75 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 127 0 127 127), good := (rows 107 107 109 104 104 104 104) }] }

theorem profile29_node30 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,17] 6 104 profile29_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,17] 6 104 profile29_node30_cert).mp (by decide +kernel))

def profile29_node31_cert : Bound 7 := { allowed := (rows 48 72 96 0 0 0 0), upper := (rows 75 50 28 105 113 97 64), lower := (rows 75 50 28 8 16 32 64), losses := [] }

theorem profile29_node31 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,24] 6 97 profile29_node31_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,24] 6 97 profile29_node31_cert).mp (by decide +kernel))

def profile29_node32_cert : Bound 7 := { allowed := (rows 48 72 72 0 0 0 0), upper := (rows 75 50 52 73 89 105 64), lower := (rows 75 50 52 8 16 32 64), losses := [] }

theorem profile29_node32 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,48] 6 73 profile29_node32_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,48] 6 73 profile29_node32_cert).mp (by decide +kernel))

def profile29_node33_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 50 69 56 56 56 64), lower := (rows 75 50 69 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 127), good := (rows 71 114 69 64 80 96 64) }] }

theorem profile29_node33 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,65] 6 56 profile29_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,65] 6 56 profile29_node33_cert).mp (by decide +kernel))

def profile29_node34_cert : Bound 7 := { allowed := (rows 48 72 48 0 0 0 0), upper := (rows 75 50 76 57 49 49 64), lower := (rows 75 50 76 8 16 32 64), losses := [] }

theorem profile29_node34 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,72] 6 49 profile29_node34_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,72] 6 49 profile29_node34_cert).mp (by decide +kernel))

def profile29_node35_cert : Bound 7 := { allowed := (rows 48 72 40 0 0 0 0), upper := (rows 75 50 84 41 57 41 64), lower := (rows 75 50 84 8 16 32 64), losses := [] }

theorem profile29_node35 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,80] 6 41 profile29_node35_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48,80] 6 41 profile29_node35_cert).mp (by decide +kernel))

def profile29_node28_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile29_node28_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile29_node28 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,48] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile29_node28_route profile29_node28_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node29
  · exact profile29_node30
  · exact profile29_node31
  · exact profile29_node32
  · exact profile29_node33
  · exact profile29_node34
  · exact profile29_node35

def profile29_node36_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 67 60 56 56 56 64), lower := (rows 75 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 67 67 68 64 80 96 64) }] }

theorem profile29_node36 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,65] 6 56 profile29_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,65] 6 56 profile29_node36_cert).mp (by decide +kernel))

def profile29_node37_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 75 74 53 57 49 49 64), lower := (rows 75 74 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 119 66 68 64 80 96 64) }] }

theorem profile29_node37 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,72] 6 49 profile29_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,72] 6 49 profile29_node37_cert).mp (by decide +kernel))

def profile29_node38_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 75 82 61 57 57 57 64), lower := (rows 75 82 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 127), good := (rows 67 82 68 64 82 96 64) }] }

theorem profile29_node38 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,80] 6 57 profile29_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74,80] 6 57 profile29_node38_cert).mp (by decide +kernel))

def profile29_node18_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile29_node18_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile29_node18 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [74] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile29_node18_route profile29_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node19
  · exact profile29_node20
  · exact profile29_node27
  · exact profile29_node28
  · exact profile29_node36
  · exact profile29_node37
  · exact profile29_node38

def profile29_node40_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 11 118 122 114 114 64), lower := (rows 89 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 127), good := (rows 81 119 68 64 80 96 64) }] }

theorem profile29_node40 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,9] 6 114 profile29_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,9] 6 114 profile29_node40_cert).mp (by decide +kernel))

def profile29_node41_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 89 26 103 107 115 99 64), lower := (rows 89 26 4 8 16 32 64), losses := [{ target := 5, region := (rows 3 3 4 8 16 0 127), good := (rows 91 91 68 72 80 64 64) }] }

theorem profile29_node41 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,24] 6 99 profile29_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,24] 6 99 profile29_node41_cert).mp (by decide +kernel))

def profile29_node43_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 35 14 120 112 112 64), lower := (rows 89 35 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 127 127 127), good := (rows 115 115 118 112 112 112 112) }] }

theorem profile29_node43 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,10] 6 112 profile29_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,10] 6 112 profile29_node43_cert).mp (by decide +kernel))

def profile29_node44_cert : Bound 7 := { allowed := (rows 32 88 96 0 0 0 0), upper := (rows 89 35 28 106 114 98 64), lower := (rows 89 35 28 8 16 32 64), losses := [] }

theorem profile29_node44 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,24] 6 98 profile29_node44_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,24] 6 98 profile29_node44_cert).mp (by decide +kernel))

def profile29_node45_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 35 38 88 88 120 64), lower := (rows 89 35 38 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 127), good := (rows 81 103 102 64 80 96 64) }] }

theorem profile29_node45 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,34] 6 88 profile29_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,34] 6 88 profile29_node45_cert).mp (by decide +kernel))

def profile29_node46_cert : Bound 7 := { allowed := (rows 32 88 80 0 0 0 0), upper := (rows 89 35 44 90 82 114 64), lower := (rows 89 35 44 8 16 32 64), losses := [] }

theorem profile29_node46 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,40] 6 82 profile29_node46_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,40] 6 82 profile29_node46_cert).mp (by decide +kernel))

def profile29_node47_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 35 70 56 56 56 64), lower := (rows 89 35 70 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 127), good := (rows 81 103 70 64 80 96 64) }] }

theorem profile29_node47 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,66] 6 56 profile29_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,66] 6 56 profile29_node47_cert).mp (by decide +kernel))

def profile29_node48_cert : Bound 7 := { allowed := (rows 32 88 48 0 0 0 0), upper := (rows 89 35 76 58 50 50 64), lower := (rows 89 35 76 8 16 32 64), losses := [] }

theorem profile29_node48 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,72] 6 50 profile29_node48_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,72] 6 50 profile29_node48_cert).mp (by decide +kernel))

def profile29_node49_cert : Bound 7 := { allowed := (rows 32 88 24 0 0 0 0), upper := (rows 89 35 100 26 26 58 64), lower := (rows 89 35 100 8 16 32 64), losses := [] }

theorem profile29_node49 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,96] 6 26 profile29_node49_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33,96] 6 26 profile29_node49_cert).mp (by decide +kernel))

def profile29_node42_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile29_node42_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node42 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,33] 6 (by decide) (choices 2) [10,24,34,40,66,72,96] profile29_node42_route profile29_node42_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node43
  · exact profile29_node44
  · exact profile29_node45
  · exact profile29_node46
  · exact profile29_node47
  · exact profile29_node48
  · exact profile29_node49

def profile29_node52_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 89 42 7 24 112 96 64), lower := (rows 89 42 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 11 5 8 0 127 127), good := (rows 111 106 103 106 96 96 96) }] }

theorem profile29_node52 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,16] 6 96 profile29_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,16] 6 96 profile29_node52_cert).mp (by decide +kernel))

def profile29_node53_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 89 42 7 40 80 112 64), lower := (rows 89 42 7 40 16 32 64), losses := [{ target := 4, region := (rows 1 42 5 42 0 32 127), good := (rows 79 106 79 106 64 106 64) }] }

theorem profile29_node53 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,32] 6 80 profile29_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,32] 6 80 profile29_node53_cert).mp (by decide +kernel))

def profile29_node54_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 89 42 7 72 48 48 64), lower := (rows 89 42 7 72 16 32 64), losses := [{ target := 4, region := (rows 1 34 4 127 0 32 127), good := (rows 73 106 79 72 72 106 72) }] }

theorem profile29_node54 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,64] 6 48 profile29_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3,64] 6 48 profile29_node54_cert).mp (by decide +kernel))

def profile29_node51_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | _ => 0

def profile29_node51_route : Route 7 := (fun mask => (mask,id))

theorem profile29_node51 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,3] 6 (by decide) (choices 1) [16,32,64] profile29_node51_route profile29_node51_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node52
  · exact profile29_node53
  · exact profile29_node54

def profile29_node55_cert : Bound 7 := { allowed := (rows 32 80 104 0 0 0 0), upper := (rows 89 42 21 106 114 98 64), lower := (rows 89 42 21 8 16 32 64), losses := [] }

theorem profile29_node55 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,17] 6 98 profile29_node55_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,17] 6 98 profile29_node55_cert).mp (by decide +kernel))

def profile29_node56_cert : Bound 7 := { allowed := (rows 32 80 104 0 0 0 0), upper := (rows 89 42 22 105 113 97 64), lower := (rows 89 42 22 8 16 32 64), losses := [] }

theorem profile29_node56 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,18] 6 97 profile29_node56_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,18] 6 97 profile29_node56_cert).mp (by decide +kernel))

def profile29_node57_cert : Bound 7 := { allowed := (rows 32 80 88 0 0 0 0), upper := (rows 89 42 37 90 82 114 64), lower := (rows 89 42 37 8 16 32 64), losses := [] }

theorem profile29_node57 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,33] 6 82 profile29_node57_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,33] 6 82 profile29_node57_cert).mp (by decide +kernel))

def profile29_node58_cert : Bound 7 := { allowed := (rows 32 80 88 0 0 0 0), upper := (rows 89 42 38 89 81 113 64), lower := (rows 89 42 38 8 16 32 64), losses := [] }

theorem profile29_node58 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,34] 6 81 profile29_node58_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,34] 6 81 profile29_node58_cert).mp (by decide +kernel))

def profile29_node59_cert : Bound 7 := { allowed := (rows 32 80 72 0 0 0 0), upper := (rows 89 42 52 75 83 99 64), lower := (rows 89 42 52 8 16 32 64), losses := [] }

theorem profile29_node59 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,48] 6 67 profile29_node59_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,48] 6 67 profile29_node59_cert).mp (by decide +kernel))

def profile29_node60_cert : Bound 7 := { allowed := (rows 32 80 56 0 0 0 0), upper := (rows 89 42 69 58 50 50 64), lower := (rows 89 42 69 8 16 32 64), losses := [] }

theorem profile29_node60 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,65] 6 50 profile29_node60_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,65] 6 50 profile29_node60_cert).mp (by decide +kernel))

def profile29_node61_cert : Bound 7 := { allowed := (rows 32 80 56 0 0 0 0), upper := (rows 89 42 70 57 49 49 64), lower := (rows 89 42 70 8 16 32 64), losses := [] }

theorem profile29_node61 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,66] 6 49 profile29_node61_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,66] 6 49 profile29_node61_cert).mp (by decide +kernel))

def profile29_node62_cert : Bound 7 := { allowed := (rows 32 80 40 0 0 0 0), upper := (rows 89 42 84 43 51 35 64), lower := (rows 89 42 84 8 16 32 64), losses := [] }

theorem profile29_node62 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,80] 6 35 profile29_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,80] 6 35 profile29_node62_cert).mp (by decide +kernel))

def profile29_node63_cert : Bound 7 := { allowed := (rows 32 80 24 0 0 0 0), upper := (rows 89 42 100 27 19 51 64), lower := (rows 89 42 100 8 16 32 64), losses := [] }

theorem profile29_node63 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,96] 6 19 profile29_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40,96] 6 19 profile29_node63_cert).mp (by decide +kernel))

def profile29_node50_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile29_node50_route : Route 7 := (fun mask => (mask,id))

theorem profile29_node50 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,40] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile29_node50_route profile29_node50_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node51
  · exact profile29_node55
  · exact profile29_node56
  · exact profile29_node57
  · exact profile29_node58
  · exact profile29_node59
  · exact profile29_node60
  · exact profile29_node61
  · exact profile29_node62
  · exact profile29_node63

def profile29_node64_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 67 62 58 58 58 64), lower := (rows 89 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 83 67 68 64 80 96 64) }] }

theorem profile29_node64 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,65] 6 58 profile29_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,65] 6 58 profile29_node64_cert).mp (by decide +kernel))

def profile29_node65_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 89 74 55 59 51 51 64), lower := (rows 89 74 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 11 4 8 0 32 127), good := (rows 75 74 68 74 64 96 64) }] }

theorem profile29_node65 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,72] 6 51 profile29_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,72] 6 51 profile29_node65_cert).mp (by decide +kernel))

def profile29_node66_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 98 63 59 59 59 64), lower := (rows 89 98 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 127), good := (rows 81 98 68 64 80 98 64) }] }

theorem profile29_node66 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,96] 6 59 profile29_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88,96] 6 59 profile29_node66_cert).mp (by decide +kernel))

def profile29_node39_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile29_node39_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node39 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [88] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile29_node39_route profile29_node39_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node40
  · exact profile29_node41
  · exact profile29_node42
  · exact profile29_node50
  · exact profile29_node64
  · exact profile29_node65
  · exact profile29_node66

def profile29_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | _ => 0

def profile29_node0_route : Route 7 := (fun mask => match mask with | 42 => (26,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 50 => (26,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 82 => (74,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 98 => (74,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 104 => (88,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 112 => (88,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node0 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [] 6 (by decide) (choices 3) [26,56,74,88] profile29_node0_route profile29_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node1
  · exact profile29_node13
  · exact profile29_node18
  · exact profile29_node39

theorem profile29 : Upper (D (n:=7) [49,33,32,18,18,18,2]) (R (n:=7) [49,33,32,18,18,18,2]) [] 6 := profile29_node0


#print axioms profile29
end Delivery.SmallBudgetTenFinite7
