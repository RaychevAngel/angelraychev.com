import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile13_node3_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 15 19 52 104 112 32 64), lower := (rows 15 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) }] }

theorem profile13_node3 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,48] 6 96 profile13_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,48] 6 96 profile13_node3_cert).mp (by decide +kernel))

def profile13_node4_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 15 19 100 120 112 32 64), lower := (rows 15 19 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 8 0 127 127), good := (rows 111 103 100 108 100 100 100) }] }

theorem profile13_node4 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,96] 6 112 profile13_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17,96] 6 112 profile13_node4_cert).mp (by decide +kernel))

def profile13_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node2_route : Route 7 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node2 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,17] 6 (by decide) (choices 2) [48,96] profile13_node2_route profile13_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node3
  · exact profile13_node4

def profile13_node5_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 15 35 116 120 112 32 64), lower := (rows 15 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 111 99 100 104 96 96 96) }] }

theorem profile13_node5 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,33] 6 112 profile13_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,33] 6 112 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : CutBound 7 := { lost := (rows 0 64 0 0 0 0 0), upper := (rows 15 50 117 121 113 32 64), lower := (rows 15 50 4 8 16 32 64), losses := [{ target := 6, region := (rows 1 18 4 8 16 127 0), good := (rows 47 50 36 40 50 32 32) }] }

theorem profile13_node6 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,48] 6 113 profile13_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,48] 6 113 profile13_node6_cert).mp (by decide +kernel))

def profile13_node7_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 15 98 117 121 113 32 64), lower := (rows 15 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 111 98 102 106 98 98 98) }] }

theorem profile13_node7 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,96] 6 113 profile13_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14,96] 6 113 profile13_node7_cert).mp (by decide +kernel))

def profile13_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node1 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [14] 6 (by decide) (choices 2) [17,33,48,96] profile13_node1_route profile13_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node5
  · exact profile13_node6
  · exact profile13_node7

def profile13_node10_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 23 11 52 104 112 32 64), lower := (rows 23 11 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) }] }

theorem profile13_node10 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,48] 6 96 profile13_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,48] 6 96 profile13_node10_cert).mp (by decide +kernel))

def profile13_node11_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 23 11 100 120 112 32 64), lower := (rows 23 11 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 8 0 127 127), good := (rows 103 111 100 108 100 100 100) }] }

theorem profile13_node11 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,96] 6 112 profile13_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9,96] 6 112 profile13_node11_cert).mp (by decide +kernel))

def profile13_node9_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node9_route : Route 7 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node9 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,9] 6 (by decide) (choices 2) [48,96] profile13_node9_route profile13_node9_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node10
  · exact profile13_node11

def profile13_node12_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 19 108 104 120 32 64), lower := (rows 23 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 127 0 127 127), good := (rows 111 111 108 108 108 108 108) }] }

theorem profile13_node12 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,17] 6 104 profile13_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,17] 6 104 profile13_node12_cert).mp (by decide +kernel))

def profile13_node13_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 26 101 105 113 32 64), lower := (rows 23 26 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 106 100 104 96 96 96) }] }

theorem profile13_node13 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,24] 6 97 profile13_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,24] 6 97 profile13_node13_cert).mp (by decide +kernel))

def profile13_node14_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 23 35 124 120 120 32 64), lower := (rows 23 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) }] }

theorem profile13_node14 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,33] 6 120 profile13_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,33] 6 120 profile13_node14_cert).mp (by decide +kernel))

def profile13_node15_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 23 42 117 121 113 32 64), lower := (rows 23 42 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 4 8 0 127 127), good := (rows 103 106 100 106 96 96 96) }] }

theorem profile13_node15 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,40] 6 113 profile13_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,40] 6 113 profile13_node15_cert).mp (by decide +kernel))

def profile13_node16_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 50 109 105 121 32 64), lower := (rows 23 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile13_node16 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,48] 6 105 profile13_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,48] 6 105 profile13_node16_cert).mp (by decide +kernel))

def profile13_node17_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 23 98 125 121 121 32 64), lower := (rows 23 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 103 98 102 106 98 98 98) }] }

theorem profile13_node17 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,96] 6 121 profile13_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22,96] 6 121 profile13_node17_cert).mp (by decide +kernel))

def profile13_node8_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile13_node8_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node8 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [22] 6 (by decide) (choices 2) [9,17,24,33,40,48,96] profile13_node8_route profile13_node8_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node9
  · exact profile13_node12
  · exact profile13_node13
  · exact profile13_node14
  · exact profile13_node15
  · exact profile13_node16
  · exact profile13_node17

def profile13_node20_cert : CutBound 7 := { lost := (rows 0 32 0 32 0 0 0), upper := (rows 39 11 52 88 80 32 64), lower := (rows 39 11 52 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 127 127 0 127), good := (rows 95 91 92 88 88 88 88) }] }

theorem profile13_node20 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,48] 6 80 profile13_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,48] 6 80 profile13_node20_cert).mp (by decide +kernel))

def profile13_node21_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 39 11 84 120 112 32 64), lower := (rows 39 11 84 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 127), good := (rows 71 75 84 72 84 64 64) }] }

theorem profile13_node21 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,80] 6 112 profile13_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,80] 6 112 profile13_node21_cert).mp (by decide +kernel))

def profile13_node22_cert : CutBound 7 := { lost := (rows 16 16 16 0 0 0 0), upper := (rows 39 11 100 88 80 32 64), lower := (rows 39 11 100 8 16 32 64), losses := [{ target := 4, region := (rows 11 10 127 8 0 127 127), good := (rows 103 111 100 111 100 100 100) }] }

theorem profile13_node22 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,96] 6 80 profile13_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9,96] 6 80 profile13_node22_cert).mp (by decide +kernel))

def profile13_node19_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node19_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node19 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,9] 6 (by decide) (choices 2) [48,80,96] profile13_node19_route profile13_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node20
  · exact profile13_node21
  · exact profile13_node22

def profile13_node24_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 19 28 104 112 32 64), lower := (rows 39 19 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) }] }

theorem profile13_node24 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,24] 6 96 profile13_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,24] 6 96 profile13_node24_cert).mp (by decide +kernel))

def profile13_node25_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 39 19 44 88 80 32 64), lower := (rows 39 19 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 103 99 108 108 96 96 96) }] }

theorem profile13_node25 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,40] 6 80 profile13_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,40] 6 80 profile13_node25_cert).mp (by decide +kernel))

def profile13_node26_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 19 52 72 88 32 64), lower := (rows 39 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) }] }

theorem profile13_node26 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,48] 6 72 profile13_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,48] 6 72 profile13_node26_cert).mp (by decide +kernel))

def profile13_node27_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 39 19 76 120 112 32 64), lower := (rows 39 19 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 103 99 108 108 96 96 96) }] }

theorem profile13_node27 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,72] 6 112 profile13_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,72] 6 112 profile13_node27_cert).mp (by decide +kernel))

def profile13_node28_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 19 84 104 120 32 64), lower := (rows 39 19 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 108 104 104 104 104) }] }

theorem profile13_node28 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,80] 6 104 profile13_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,80] 6 104 profile13_node28_cert).mp (by decide +kernel))

def profile13_node29_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 39 19 100 88 88 32 64), lower := (rows 39 19 100 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile13_node29 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,96] 6 88 profile13_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17,96] 6 88 profile13_node29_cert).mp (by decide +kernel))

def profile13_node23_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile13_node23_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node23 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,17] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile13_node23_route profile13_node23_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node24
  · exact profile13_node25
  · exact profile13_node26
  · exact profile13_node27
  · exact profile13_node28
  · exact profile13_node29

def profile13_node31_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 26 21 104 112 32 64), lower := (rows 39 26 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 106 109 104 104 104 104) }] }

theorem profile13_node31 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,17] 6 96 profile13_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,17] 6 96 profile13_node31_cert).mp (by decide +kernel))

def profile13_node32_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 39 26 37 88 80 32 64), lower := (rows 39 26 37 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 111 101 104 96 96 96) }] }

theorem profile13_node32 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,33] 6 80 profile13_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,33] 6 80 profile13_node32_cert).mp (by decide +kernel))

def profile13_node33_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 26 52 73 81 32 64), lower := (rows 39 26 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 106 100 104 96 96 96) }] }

theorem profile13_node33 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,48] 6 65 profile13_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,48] 6 65 profile13_node33_cert).mp (by decide +kernel))

def profile13_node34_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 39 26 69 120 112 32 64), lower := (rows 39 26 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 111 101 104 96 96 96) }] }

theorem profile13_node34 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,65] 6 112 profile13_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,65] 6 112 profile13_node34_cert).mp (by decide +kernel))

def profile13_node35_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 39 26 84 105 113 32 64), lower := (rows 39 26 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 106 100 104 96 96 96) }] }

theorem profile13_node35 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,80] 6 97 profile13_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,80] 6 97 profile13_node35_cert).mp (by decide +kernel))

def profile13_node36_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 39 26 100 89 81 32 64), lower := (rows 39 26 100 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 111 100 108 100 100 100) }] }

theorem profile13_node36 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,96] 6 81 profile13_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24,96] 6 81 profile13_node36_cert).mp (by decide +kernel))

def profile13_node30_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node30_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node30 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,24] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile13_node30_route profile13_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node31
  · exact profile13_node32
  · exact profile13_node33
  · exact profile13_node34
  · exact profile13_node35
  · exact profile13_node36

def profile13_node37_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 35 92 88 88 32 64), lower := (rows 39 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile13_node37 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,33] 6 88 profile13_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,33] 6 88 profile13_node37_cert).mp (by decide +kernel))

def profile13_node38_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 39 42 85 89 81 32 64), lower := (rows 39 42 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 4 8 0 127 127), good := (rows 103 106 100 106 96 96 96) }] }

theorem profile13_node38 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,40] 6 81 profile13_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,40] 6 81 profile13_node38_cert).mp (by decide +kernel))

def profile13_node39_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 39 50 93 89 89 32 64), lower := (rows 39 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile13_node39 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,48] 6 89 profile13_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,48] 6 89 profile13_node39_cert).mp (by decide +kernel))

def profile13_node40_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 67 124 120 120 32 64), lower := (rows 39 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile13_node40 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,65] 6 120 profile13_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,65] 6 120 profile13_node40_cert).mp (by decide +kernel))

def profile13_node41_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 39 74 117 121 113 32 64), lower := (rows 39 74 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 4 8 0 127 127), good := (rows 103 106 100 106 96 96 96) }] }

theorem profile13_node41 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,72] 6 113 profile13_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,72] 6 113 profile13_node41_cert).mp (by decide +kernel))

def profile13_node42_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 39 82 125 121 121 32 64), lower := (rows 39 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 71 82 68 72 82 64 64) }] }

theorem profile13_node42 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,80] 6 121 profile13_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,80] 6 121 profile13_node42_cert).mp (by decide +kernel))

def profile13_node43_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 98 93 89 89 32 64), lower := (rows 39 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 127 4 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile13_node43 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,96] 6 89 profile13_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38,96] 6 89 profile13_node43_cert).mp (by decide +kernel))

def profile13_node18_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile13_node18_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node18 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [38] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile13_node18_route profile13_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node19
  · exact profile13_node23
  · exact profile13_node30
  · exact profile13_node37
  · exact profile13_node38
  · exact profile13_node39
  · exact profile13_node40
  · exact profile13_node41
  · exact profile13_node42
  · exact profile13_node43

def profile13_node46_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 51 7 28 104 112 32 64), lower := (rows 51 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) }] }

theorem profile13_node46 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,24] 6 96 profile13_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,24] 6 96 profile13_node46_cert).mp (by decide +kernel))

def profile13_node47_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 51 7 44 88 80 32 64), lower := (rows 51 7 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 99 103 108 108 96 96 96) }] }

theorem profile13_node47 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,40] 6 80 profile13_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,40] 6 80 profile13_node47_cert).mp (by decide +kernel))

def profile13_node48_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 51 7 52 72 88 32 64), lower := (rows 51 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) }] }

theorem profile13_node48 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,48] 6 72 profile13_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,48] 6 72 profile13_node48_cert).mp (by decide +kernel))

def profile13_node49_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 51 7 76 120 112 32 64), lower := (rows 51 7 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 99 103 108 108 96 96 96) }] }

theorem profile13_node49 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,72] 6 112 profile13_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,72] 6 112 profile13_node49_cert).mp (by decide +kernel))

def profile13_node50_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 51 7 84 104 120 32 64), lower := (rows 51 7 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 108 104 104 104 104) }] }

theorem profile13_node50 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,80] 6 104 profile13_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,80] 6 104 profile13_node50_cert).mp (by decide +kernel))

def profile13_node51_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 51 7 100 88 88 32 64), lower := (rows 51 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile13_node51 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,96] 6 88 profile13_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5,96] 6 88 profile13_node51_cert).mp (by decide +kernel))

def profile13_node45_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile13_node45_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node45 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,5] 6 (by decide) (choices 2) [24,40,48,72,80,96] profile13_node45_route profile13_node45_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node46
  · exact profile13_node47
  · exact profile13_node48
  · exact profile13_node49
  · exact profile13_node50
  · exact profile13_node51

def profile13_node53_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 51 14 21 104 112 32 64), lower := (rows 51 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 127 0 127 127), good := (rows 107 110 111 104 104 104 104) }] }

theorem profile13_node53 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,17] 6 96 profile13_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,17] 6 96 profile13_node53_cert).mp (by decide +kernel))

def profile13_node54_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 51 14 37 88 80 32 64), lower := (rows 51 14 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 103 110 101 104 96 96 96) }] }

theorem profile13_node54 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,33] 6 80 profile13_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,33] 6 80 profile13_node54_cert).mp (by decide +kernel))

def profile13_node55_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 51 14 52 73 81 32 64), lower := (rows 51 14 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 107 110 100 104 96 96 96) }] }

theorem profile13_node55 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,48] 6 65 profile13_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,48] 6 65 profile13_node55_cert).mp (by decide +kernel))

def profile13_node56_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 51 14 69 120 112 32 64), lower := (rows 51 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 103 110 101 104 96 96 96) }] }

theorem profile13_node56 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,65] 6 112 profile13_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,65] 6 112 profile13_node56_cert).mp (by decide +kernel))

def profile13_node57_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 51 14 84 105 113 32 64), lower := (rows 51 14 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 107 110 100 104 96 96 96) }] }

theorem profile13_node57 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,80] 6 97 profile13_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,80] 6 97 profile13_node57_cert).mp (by decide +kernel))

def profile13_node58_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 51 14 100 89 81 32 64), lower := (rows 51 14 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 127 8 0 127 127), good := (rows 103 110 100 110 100 100 100) }] }

theorem profile13_node58 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,96] 6 81 profile13_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12,96] 6 81 profile13_node58_cert).mp (by decide +kernel))

def profile13_node52_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node52_route : Route 7 := (fun mask => (mask,id))

theorem profile13_node52 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,12] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile13_node52_route profile13_node52_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node53
  · exact profile13_node54
  · exact profile13_node55
  · exact profile13_node56
  · exact profile13_node57
  · exact profile13_node58

def profile13_node59_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 19 108 108 124 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 127 127 0 127 127), good := (rows 111 111 108 108 108 108 108) }] }

theorem profile13_node59 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,17] 6 108 profile13_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,17] 6 108 profile13_node59_cert).mp (by decide +kernel))

def profile13_node60_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 22 109 105 121 32 64), lower := (rows 51 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 102 100 104 96 96 96) }] }

theorem profile13_node60 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,20] 6 105 profile13_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,20] 6 105 profile13_node60_cert).mp (by decide +kernel))

def profile13_node61_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 35 92 92 92 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile13_node61 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,33] 6 92 profile13_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,33] 6 92 profile13_node61_cert).mp (by decide +kernel))

def profile13_node62_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 38 93 89 89 32 64), lower := (rows 51 38 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) }] }

theorem profile13_node62 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,36] 6 89 profile13_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,36] 6 89 profile13_node62_cert).mp (by decide +kernel))

def profile13_node63_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 50 77 77 93 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile13_node63 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,48] 6 77 profile13_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,48] 6 77 profile13_node63_cert).mp (by decide +kernel))

def profile13_node64_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 67 124 124 124 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile13_node64 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,65] 6 124 profile13_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,65] 6 124 profile13_node64_cert).mp (by decide +kernel))

def profile13_node65_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 70 125 121 121 32 64), lower := (rows 51 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) }] }

theorem profile13_node65 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,68] 6 121 profile13_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,68] 6 121 profile13_node65_cert).mp (by decide +kernel))

def profile13_node66_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 82 109 109 125 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile13_node66 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,80] 6 109 profile13_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,80] 6 109 profile13_node66_cert).mp (by decide +kernel))

def profile13_node67_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 98 93 93 93 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile13_node67 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,96] 6 93 profile13_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50,96] 6 93 profile13_node67_cert).mp (by decide +kernel))

def profile13_node44_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile13_node44_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile13_node44 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [50] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,65,68,80,96] profile13_node44_route profile13_node44_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node45
  · exact profile13_node52
  · exact profile13_node59
  · exact profile13_node60
  · exact profile13_node61
  · exact profile13_node62
  · exact profile13_node63
  · exact profile13_node64
  · exact profile13_node65
  · exact profile13_node66
  · exact profile13_node67

def profile13_node68_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 99 127 125 125 125 32 64), lower := (rows 99 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile13_node68 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [98] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [98] 6 125 profile13_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [98] 6 125 profile13_node68_cert).mp (by decide +kernel))

def profile13_node72_cert : CutBound 7 := { lost := (rows 0 64 64 64 0 0 0), upper := (rows 113 7 14 56 80 32 64), lower := (rows 113 7 14 56 16 32 64), losses := [{ target := 6, region := (rows 1 3 7 25 16 127 0), good := (rows 63 47 46 56 56 32 32) }] }

theorem profile13_node72 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,48] 6 64 profile13_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,48] 6 64 profile13_node72_cert).mp (by decide +kernel))

def profile13_node73_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 113 7 14 104 16 32 64), lower := (rows 113 7 14 104 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 127 0 127 127), good := (rows 111 111 110 104 104 104 104) }] }

theorem profile13_node73 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,96] 6 16 profile13_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10,96] 6 16 profile13_node73_cert).mp (by decide +kernel))

def profile13_node71_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile13_node71_route : Route 7 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node71 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,10] 6 (by decide) (choices 2) [48,96] profile13_node71_route profile13_node71_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node72
  · exact profile13_node73

def profile13_node74_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 7 22 104 120 32 64), lower := (rows 113 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 111 110 104 104 104 104) }] }

theorem profile13_node74 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,18] 6 104 profile13_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,18] 6 104 profile13_node74_cert).mp (by decide +kernel))

def profile13_node75_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 7 28 106 114 32 64), lower := (rows 113 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 111 108 104 96 96 96) }] }

theorem profile13_node75 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,24] 6 98 profile13_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,24] 6 98 profile13_node75_cert).mp (by decide +kernel))

def profile13_node76_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 113 7 38 88 88 32 64), lower := (rows 113 7 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile13_node76 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,34] 6 88 profile13_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,34] 6 88 profile13_node76_cert).mp (by decide +kernel))

def profile13_node77_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 113 7 44 90 82 32 64), lower := (rows 113 7 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 97 103 108 108 96 96 96) }] }

theorem profile13_node77 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,40] 6 82 profile13_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,40] 6 82 profile13_node77_cert).mp (by decide +kernel))

def profile13_node78_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 7 52 74 90 32 64), lower := (rows 113 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile13_node78 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,48] 6 74 profile13_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,48] 6 74 profile13_node78_cert).mp (by decide +kernel))

def profile13_node79_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 113 7 100 26 26 32 64), lower := (rows 113 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile13_node79 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,96] 6 26 profile13_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5,96] 6 26 profile13_node79_cert).mp (by decide +kernel))

def profile13_node70_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile13_node70_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node70 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,5] 6 (by decide) (choices 2) [10,18,24,34,40,48,96] profile13_node70_route profile13_node70_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node71
  · exact profile13_node74
  · exact profile13_node75
  · exact profile13_node76
  · exact profile13_node77
  · exact profile13_node78
  · exact profile13_node79

def profile13_node82_cert : CutBound 7 := { lost := (rows 0 64 64 64 0 0 0), upper := (rows 113 14 7 56 80 32 64), lower := (rows 113 14 7 56 16 32 64), losses := [{ target := 6, region := (rows 1 7 5 25 16 127 0), good := (rows 63 46 47 56 56 32 32) }] }

theorem profile13_node82 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,48] 6 64 profile13_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,48] 6 64 profile13_node82_cert).mp (by decide +kernel))

def profile13_node83_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 113 14 7 104 16 32 64), lower := (rows 113 14 7 104 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 127 0 127 127), good := (rows 111 110 111 104 104 104 104) }] }

theorem profile13_node83 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,96] 6 16 profile13_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3,96] 6 16 profile13_node83_cert).mp (by decide +kernel))

def profile13_node81_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile13_node81_route : Route 7 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node81 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,3] 6 (by decide) (choices 2) [48,96] profile13_node81_route profile13_node81_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node82
  · exact profile13_node83

def profile13_node84_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 113 14 21 106 114 32 64), lower := (rows 113 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 127 127), good := (rows 97 110 111 104 96 96 96) }] }

theorem profile13_node84 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,17] 6 98 profile13_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,17] 6 98 profile13_node84_cert).mp (by decide +kernel))

def profile13_node85_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 14 22 105 113 32 64), lower := (rows 113 14 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 110 102 104 96 96 96) }] }

theorem profile13_node85 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,18] 6 97 profile13_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,18] 6 97 profile13_node85_cert).mp (by decide +kernel))

def profile13_node86_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 113 14 37 90 82 32 64), lower := (rows 113 14 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 101 110 101 104 96 96 96) }] }

theorem profile13_node86 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,33] 6 82 profile13_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,33] 6 82 profile13_node86_cert).mp (by decide +kernel))

def profile13_node87_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 113 14 38 89 81 32 64), lower := (rows 113 14 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 14 8 0 127 127), good := (rows 97 110 102 110 96 96 96) }] }

theorem profile13_node87 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,34] 6 81 profile13_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,34] 6 81 profile13_node87_cert).mp (by decide +kernel))

def profile13_node88_cert : CutBound 7 := { lost := (rows 0 0 64 0 0 0 0), upper := (rows 113 14 52 75 83 32 64), lower := (rows 113 14 52 8 16 32 64), losses := [{ target := 6, region := (rows 1 2 21 8 16 127 0), good := (rows 53 46 52 40 52 32 32) }] }

theorem profile13_node88 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,48] 6 67 profile13_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,48] 6 67 profile13_node88_cert).mp (by decide +kernel))

def profile13_node89_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 113 14 100 27 19 32 64), lower := (rows 113 14 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 127 8 0 127 127), good := (rows 101 110 100 110 100 100 100) }] }

theorem profile13_node89 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,96] 6 19 profile13_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12,96] 6 19 profile13_node89_cert).mp (by decide +kernel))

def profile13_node80_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile13_node80_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node80 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,12] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile13_node80_route profile13_node80_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node81
  · exact profile13_node84
  · exact profile13_node85
  · exact profile13_node86
  · exact profile13_node87
  · exact profile13_node88
  · exact profile13_node89

def profile13_node90_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 19 110 110 126 32 64), lower := (rows 113 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile13_node90 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,17] 6 110 profile13_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,17] 6 110 profile13_node90_cert).mp (by decide +kernel))

def profile13_node92_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 22 7 104 120 32 64), lower := (rows 113 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 110 111 104 104 104 104) }] }

theorem profile13_node92 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,3] 6 104 profile13_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,3] 6 104 profile13_node92_cert).mp (by decide +kernel))

def profile13_node93_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 22 13 106 114 32 64), lower := (rows 113 22 13 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 110 109 104 96 96 96) }] }

theorem profile13_node93 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,9] 6 98 profile13_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,9] 6 98 profile13_node93_cert).mp (by decide +kernel))

def profile13_node94_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 113 22 14 105 113 32 64), lower := (rows 113 22 14 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 102 110 104 96 96 96) }] }

theorem profile13_node94 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,10] 6 97 profile13_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,10] 6 97 profile13_node94_cert).mp (by decide +kernel))

def profile13_node95_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 22 37 74 90 32 64), lower := (rows 113 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 127 127), good := (rows 101 110 101 104 96 96 96) }] }

theorem profile13_node95 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,33] 6 74 profile13_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,33] 6 74 profile13_node95_cert).mp (by decide +kernel))

def profile13_node96_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 22 38 73 89 32 64), lower := (rows 113 22 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 9 0 127 127), good := (rows 105 102 102 104 96 96 96) }] }

theorem profile13_node96 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,34] 6 73 profile13_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,34] 6 73 profile13_node96_cert).mp (by decide +kernel))

def profile13_node97_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 113 22 44 75 83 32 64), lower := (rows 113 22 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 97 102 108 108 96 96 96) }] }

theorem profile13_node97 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,40] 6 67 profile13_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,40] 6 67 profile13_node97_cert).mp (by decide +kernel))

def profile13_node98_cert : Bound 7 := { allowed := (rows 0 96 16 112 0 0 0), upper := (rows 113 22 100 11 27 32 64), lower := (rows 113 22 100 8 16 32 64), losses := [] }

theorem profile13_node98 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,96] 6 11 profile13_node98_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20,96] 6 11 profile13_node98_cert).mp (by decide +kernel))

def profile13_node91_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile13_node91_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node91 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,20] 6 (by decide) (choices 2) [3,9,10,33,34,40,96] profile13_node91_route profile13_node91_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node92
  · exact profile13_node93
  · exact profile13_node94
  · exact profile13_node95
  · exact profile13_node96
  · exact profile13_node97
  · exact profile13_node98

def profile13_node99_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 113 35 94 94 94 32 64), lower := (rows 113 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile13_node99 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,33] 6 94 profile13_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,33] 6 94 profile13_node99_cert).mp (by decide +kernel))

def profile13_node100_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 113 38 95 91 91 32 64), lower := (rows 113 38 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 97 102 102 104 96 96 96) }] }

theorem profile13_node100 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,36] 6 91 profile13_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,36] 6 91 profile13_node100_cert).mp (by decide +kernel))

def profile13_node101_cert : CutBound 7 := { lost := (rows 0 64 0 0 0 0 0), upper := (rows 113 50 79 79 95 32 64), lower := (rows 113 50 4 8 16 32 64), losses := [{ target := 6, region := (rows 1 19 4 8 16 127 0), good := (rows 51 50 36 40 50 32 32) }] }

theorem profile13_node101 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,48] 6 79 profile13_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,48] 6 79 profile13_node101_cert).mp (by decide +kernel))

def profile13_node102_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 113 98 31 31 31 32 64), lower := (rows 113 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile13_node102 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,96] 6 31 profile13_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112,96] 6 31 profile13_node102_cert).mp (by decide +kernel))

def profile13_node69_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile13_node69_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile13_node69 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [112] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,96] profile13_node69_route profile13_node69_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node70
  · exact profile13_node80
  · exact profile13_node90
  · exact profile13_node91
  · exact profile13_node99
  · exact profile13_node100
  · exact profile13_node101
  · exact profile13_node102

def profile13_node0_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile13_node0_route : Route 7 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 42 => (38,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 74 => (38,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 44 => (38,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 76 => (38,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 100 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 56 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 88 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 104 => (98,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile13_node0 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [] 6 (by decide) (choices 3) [14,22,38,50,98,112] profile13_node0_route profile13_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node1
  · exact profile13_node8
  · exact profile13_node18
  · exact profile13_node44
  · exact profile13_node68
  · exact profile13_node69

theorem profile13 : Upper (D (n:=7) [49,33,33,33,18,2,2]) (R (n:=7) [49,33,33,33,18,2,2]) [] 6 := profile13_node0


#print axioms profile13
end Delivery.SmallBudgetTenFinite7
