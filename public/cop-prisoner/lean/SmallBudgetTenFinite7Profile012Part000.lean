import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile12_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 19 102 106 114 32 64), lower := (rows 23 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile12_node2 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,17] 6 98 profile12_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,17] 6 98 profile12_node2_cert).mp (by decide +kernel))

def profile12_node3_cert : CutBound 7 := { lost := (rows 0 80 0 0 0 0 0), upper := (rows 23 35 118 122 114 32 64), lower := (rows 23 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) },{ target := 6, region := (rows 1 3 4 8 16 127 0), good := (rows 55 35 36 40 48 32 32) }] }

theorem profile12_node3 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,33] 6 114 profile12_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,33] 6 114 profile12_node3_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 50 103 107 115 32 64), lower := (rows 23 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile12_node4 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,48] 6 99 profile12_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,48] 6 99 profile12_node4_cert).mp (by decide +kernel))

def profile12_node6_cert : CutBound 7 := { lost := (rows 0 16 16 2 0 0 0), upper := (rows 23 98 7 120 112 32 64), lower := (rows 23 98 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 120 125 120 120 120 120) },{ target := 4, region := (rows 1 127 5 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile12_node6 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,3] 6 112 profile12_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,3] 6 112 profile12_node6_cert).mp (by decide +kernel))

def profile12_node7_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 23 98 21 106 114 32 64), lower := (rows 23 98 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 117 96 117 104 112 96 96) },{ target := 4, region := (rows 1 127 4 127 0 127 127), good := (rows 111 106 111 106 106 106 106) }] }

theorem profile12_node7 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,17] 6 98 profile12_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,17] 6 98 profile12_node7_cert).mp (by decide +kernel))

def profile12_node8_cert : CutBound 7 := { lost := (rows 0 16 0 18 0 0 0), upper := (rows 23 98 22 105 113 32 64), lower := (rows 23 98 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 116 104 112 96 96) },{ target := 4, region := (rows 1 127 4 9 0 127 127), good := (rows 111 98 102 106 98 98 98) }] }

theorem profile12_node8 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,18] 6 97 profile12_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,18] 6 97 profile12_node8_cert).mp (by decide +kernel))

def profile12_node9_cert : CutBound 7 := { lost := (rows 0 16 18 0 0 0 0), upper := (rows 23 98 37 90 82 32 64), lower := (rows 23 98 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 117 96 101 104 112 96 96) },{ target := 4, region := (rows 1 127 5 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile12_node9 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,33] 6 82 profile12_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,33] 6 82 profile12_node9_cert).mp (by decide +kernel))

def profile12_node10_cert : CutBound 7 := { lost := (rows 0 16 16 2 0 0 0), upper := (rows 23 98 38 89 81 32 64), lower := (rows 23 98 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 100 104 112 96 96) },{ target := 4, region := (rows 1 127 127 8 0 127 127), good := (rows 103 102 102 110 102 102 102) }] }

theorem profile12_node10 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,34] 6 81 profile12_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,34] 6 81 profile12_node10_cert).mp (by decide +kernel))

def profile12_node11_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 23 98 52 75 83 32 64), lower := (rows 23 98 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 21 8 16 127 127), good := (rows 117 96 116 104 116 96 96) },{ target := 4, region := (rows 1 127 4 9 0 127 127), good := (rows 111 98 102 106 98 98 98) }] }

theorem profile12_node11 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,48] 6 67 profile12_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,48] 6 67 profile12_node11_cert).mp (by decide +kernel))

def profile12_node12_cert : CutBound 7 := { lost := (rows 0 16 18 0 0 0 0), upper := (rows 23 98 100 27 19 32 64), lower := (rows 23 98 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 117 100 100 108 116 100 100) },{ target := 4, region := (rows 1 127 127 8 0 127 127), good := (rows 103 102 102 110 102 102 102) }] }

theorem profile12_node12 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,96] 6 19 profile12_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96,96] 6 19 profile12_node12_cert).mp (by decide +kernel))

def profile12_node5_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node5_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node5 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22,96] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile12_node5_route profile12_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node6
  · exact profile12_node7
  · exact profile12_node8
  · exact profile12_node9
  · exact profile12_node10
  · exact profile12_node11
  · exact profile12_node12

def profile12_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node1 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [22] 6 (by decide) (choices 2) [17,33,48,96] profile12_node1_route profile12_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node4
  · exact profile12_node5

def profile12_node15_cert : CutBound 7 := { lost := (rows 16 0 0 18 0 0 0), upper := (rows 39 19 22 104 112 32 64), lower := (rows 39 19 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 124 120 120 120 120) },{ target := 4, region := (rows 5 2 4 127 0 127 127), good := (rows 111 107 111 104 104 104 104) }] }

theorem profile12_node15 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,18] 6 96 profile12_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,18] 6 96 profile12_node15_cert).mp (by decide +kernel))

def profile12_node16_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 39 19 38 88 80 32 64), lower := (rows 39 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 124 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node16 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,34] 6 80 profile12_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,34] 6 80 profile12_node16_cert).mp (by decide +kernel))

def profile12_node17_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 39 19 52 74 82 32 64), lower := (rows 39 19 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 117 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 111 107 100 104 96 96 96) }] }

theorem profile12_node17 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,48] 6 66 profile12_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,48] 6 66 profile12_node17_cert).mp (by decide +kernel))

def profile12_node18_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 39 19 70 120 112 32 64), lower := (rows 39 19 70 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 124 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node18 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,66] 6 112 profile12_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,66] 6 112 profile12_node18_cert).mp (by decide +kernel))

def profile12_node19_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 39 19 84 106 114 32 64), lower := (rows 39 19 84 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 117 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 111 107 100 104 96 96 96) }] }

theorem profile12_node19 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,80] 6 98 profile12_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,80] 6 98 profile12_node19_cert).mp (by decide +kernel))

def profile12_node20_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 39 19 100 90 82 32 64), lower := (rows 39 19 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 117 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile12_node20 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,96] 6 82 profile12_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17,96] 6 82 profile12_node20_cert).mp (by decide +kernel))

def profile12_node14_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node14_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node14 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,17] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile12_node14_route profile12_node14_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node15
  · exact profile12_node16
  · exact profile12_node17
  · exact profile12_node18
  · exact profile12_node19
  · exact profile12_node20

def profile12_node21_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 35 86 90 82 32 64), lower := (rows 39 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile12_node21 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,33] 6 82 profile12_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,33] 6 82 profile12_node21_cert).mp (by decide +kernel))

def profile12_node22_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 39 50 87 91 83 32 64), lower := (rows 39 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile12_node22 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,48] 6 83 profile12_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,48] 6 83 profile12_node22_cert).mp (by decide +kernel))

def profile12_node23_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 67 118 122 114 32 64), lower := (rows 39 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile12_node23 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,65] 6 114 profile12_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,65] 6 114 profile12_node23_cert).mp (by decide +kernel))

def profile12_node25_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 39 82 7 120 112 32 64), lower := (rows 39 82 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 120 125 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node25 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,3] 6 112 profile12_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,3] 6 112 profile12_node25_cert).mp (by decide +kernel))

def profile12_node26_cert : CutBound 7 := { lost := (rows 0 32 0 16 0 0 0), upper := (rows 39 82 21 106 114 32 64), lower := (rows 39 82 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 111 106 109 104 96 96 96) },{ target := 5, region := (rows 1 22 4 8 16 0 127), good := (rows 71 82 87 72 82 64 64) }] }

theorem profile12_node26 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,17] 6 98 profile12_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,17] 6 98 profile12_node26_cert).mp (by decide +kernel))

def profile12_node27_cert : CutBound 7 := { lost := (rows 16 0 0 18 0 0 0), upper := (rows 39 82 22 105 113 32 64), lower := (rows 39 82 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 112 116 104 112 96 96) },{ target := 4, region := (rows 5 2 4 13 0 127 127), good := (rows 111 98 111 104 96 96 96) }] }

theorem profile12_node27 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,18] 6 97 profile12_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,18] 6 97 profile12_node27_cert).mp (by decide +kernel))

def profile12_node28_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 39 82 37 90 82 32 64), lower := (rows 39 82 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 112 101 104 112 96 96) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile12_node28 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,33] 6 82 profile12_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,33] 6 82 profile12_node28_cert).mp (by decide +kernel))

def profile12_node29_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 39 82 38 89 81 32 64), lower := (rows 39 82 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 112 100 104 112 96 96) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node29 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,34] 6 81 profile12_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,34] 6 81 profile12_node29_cert).mp (by decide +kernel))

def profile12_node30_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 39 82 52 75 83 32 64), lower := (rows 39 82 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 116 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile12_node30 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,48] 6 67 profile12_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,48] 6 67 profile12_node30_cert).mp (by decide +kernel))

def profile12_node31_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 39 82 69 58 50 32 64), lower := (rows 39 82 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 112 101 104 112 96 96) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile12_node31 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,65] 6 50 profile12_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,65] 6 50 profile12_node31_cert).mp (by decide +kernel))

def profile12_node32_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 39 82 70 57 49 32 64), lower := (rows 39 82 70 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 112 100 104 112 96 96) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node32 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,66] 6 49 profile12_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,66] 6 49 profile12_node32_cert).mp (by decide +kernel))

def profile12_node33_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 39 82 84 43 51 32 64), lower := (rows 39 82 84 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 116 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile12_node33 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,80] 6 35 profile12_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,80] 6 35 profile12_node33_cert).mp (by decide +kernel))

def profile12_node34_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 39 82 100 27 19 32 64), lower := (rows 39 82 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 116 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile12_node34 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,96] 6 19 profile12_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80,96] 6 19 profile12_node34_cert).mp (by decide +kernel))

def profile12_node24_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node24_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node24 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,80] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile12_node24_route profile12_node24_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node25
  · exact profile12_node26
  · exact profile12_node27
  · exact profile12_node28
  · exact profile12_node29
  · exact profile12_node30
  · exact profile12_node31
  · exact profile12_node32
  · exact profile12_node33
  · exact profile12_node34

def profile12_node35_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 98 87 91 83 32 64), lower := (rows 39 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 127 4 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile12_node35 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,96] 6 83 profile12_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38,96] 6 83 profile12_node35_cert).mp (by decide +kernel))

def profile12_node13_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node13_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node13 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [38] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile12_node13_route profile12_node13_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node14
  · exact profile12_node21
  · exact profile12_node22
  · exact profile12_node23
  · exact profile12_node24
  · exact profile12_node35

def profile12_node38_cert : CutBound 7 := { lost := (rows 0 0 0 18 0 0 0), upper := (rows 51 7 22 104 112 32 64), lower := (rows 51 7 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 124 120 120 120 120) },{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 107 111 110 104 104 104 104) }] }

theorem profile12_node38 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,18] 6 96 profile12_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,18] 6 96 profile12_node38_cert).mp (by decide +kernel))

def profile12_node39_cert : CutBound 7 := { lost := (rows 0 16 16 2 0 0 0), upper := (rows 51 7 38 88 80 32 64), lower := (rows 51 7 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 124 120 120 120 120) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile12_node39 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,34] 6 80 profile12_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,34] 6 80 profile12_node39_cert).mp (by decide +kernel))

def profile12_node40_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 51 7 52 74 82 32 64), lower := (rows 51 7 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 21 8 16 127 127), good := (rows 117 101 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 107 111 100 104 96 96 96) }] }

theorem profile12_node40 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,48] 6 66 profile12_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,48] 6 66 profile12_node40_cert).mp (by decide +kernel))

def profile12_node41_cert : CutBound 7 := { lost := (rows 0 16 16 2 0 0 0), upper := (rows 51 7 70 120 112 32 64), lower := (rows 51 7 70 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 124 120 120 120 120) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile12_node41 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,66] 6 112 profile12_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,66] 6 112 profile12_node41_cert).mp (by decide +kernel))

def profile12_node42_cert : CutBound 7 := { lost := (rows 0 0 2 16 0 0 0), upper := (rows 51 7 84 106 114 32 64), lower := (rows 51 7 84 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 21 8 16 127 127), good := (rows 117 101 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 107 111 100 104 96 96 96) }] }

theorem profile12_node42 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,80] 6 98 profile12_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,80] 6 98 profile12_node42_cert).mp (by decide +kernel))

def profile12_node43_cert : CutBound 7 := { lost := (rows 0 16 18 0 0 0 0), upper := (rows 51 7 100 90 82 32 64), lower := (rows 51 7 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 117 101 100 108 116 100 100) },{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile12_node43 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,96] 6 82 profile12_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5,96] 6 82 profile12_node43_cert).mp (by decide +kernel))

def profile12_node37_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node37_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node37 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,5] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile12_node37_route profile12_node37_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node38
  · exact profile12_node39
  · exact profile12_node40
  · exact profile12_node41
  · exact profile12_node42
  · exact profile12_node43

def profile12_node44_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 19 102 110 118 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile12_node44 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,17] 6 102 profile12_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,17] 6 102 profile12_node44_cert).mp (by decide +kernel))

def profile12_node45_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 22 103 107 115 32 64), lower := (rows 51 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 102 100 104 96 96 96) }] }

theorem profile12_node45 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,20] 6 99 profile12_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,20] 6 99 profile12_node45_cert).mp (by decide +kernel))

def profile12_node46_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 51 35 86 94 86 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile12_node46 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,33] 6 86 profile12_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,33] 6 86 profile12_node46_cert).mp (by decide +kernel))

def profile12_node47_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 51 38 87 91 83 32 64), lower := (rows 51 38 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) }] }

theorem profile12_node47 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,36] 6 83 profile12_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,36] 6 83 profile12_node47_cert).mp (by decide +kernel))

def profile12_node48_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 50 71 79 87 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile12_node48 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,48] 6 71 profile12_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,48] 6 71 profile12_node48_cert).mp (by decide +kernel))

def profile12_node49_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 51 67 118 126 118 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile12_node49 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,65] 6 118 profile12_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,65] 6 118 profile12_node49_cert).mp (by decide +kernel))

def profile12_node50_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 51 70 119 123 115 32 64), lower := (rows 51 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 83 70 70 72 80 64 64) }] }

theorem profile12_node50 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,68] 6 115 profile12_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,68] 6 115 profile12_node50_cert).mp (by decide +kernel))

def profile12_node51_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 82 103 111 119 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile12_node51 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,80] 6 103 profile12_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,80] 6 103 profile12_node51_cert).mp (by decide +kernel))

def profile12_node52_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 51 98 87 95 87 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile12_node52 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,96] 6 87 profile12_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50,96] 6 87 profile12_node52_cert).mp (by decide +kernel))

def profile12_node36_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node36_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node36 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [50] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile12_node36_route profile12_node36_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node37
  · exact profile12_node44
  · exact profile12_node45
  · exact profile12_node46
  · exact profile12_node47
  · exact profile12_node48
  · exact profile12_node49
  · exact profile12_node50
  · exact profile12_node51
  · exact profile12_node52

def profile12_node54_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 53 19 102 106 114 32 64), lower := (rows 53 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 101 111 100 104 96 96 96) }] }

theorem profile12_node54 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,17] 6 98 profile12_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,17] 6 98 profile12_node54_cert).mp (by decide +kernel))

def profile12_node55_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 53 35 86 90 82 32 64), lower := (rows 53 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 85 95 68 72 80 64 64) }] }

theorem profile12_node55 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,33] 6 82 profile12_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,33] 6 82 profile12_node55_cert).mp (by decide +kernel))

def profile12_node57_cert : CutBound 7 := { lost := (rows 0 0 0 48 0 0 0), upper := (rows 53 50 7 74 82 32 64), lower := (rows 53 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 14 0 127 127), good := (rows 109 106 111 104 96 96 96) },{ target := 5, region := (rows 1 2 4 14 22 0 127), good := (rows 93 90 95 72 80 64 64) }] }

theorem profile12_node57 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,3] 6 66 profile12_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,3] 6 66 profile12_node57_cert).mp (by decide +kernel))

def profile12_node58_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 50 69 74 82 32 64), lower := (rows 53 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 127 127), good := (rows 117 117 101 104 117 96 96) }] }

theorem profile12_node58 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,65] 6 66 profile12_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,65] 6 66 profile12_node58_cert).mp (by decide +kernel))

def profile12_node59_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 53 50 70 75 83 32 64), lower := (rows 53 50 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 127 127), good := (rows 101 102 102 104 96 96 96) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 85 86 70 72 80 64 64) }] }

theorem profile12_node59 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,66] 6 67 profile12_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48,66] 6 67 profile12_node59_cert).mp (by decide +kernel))

def profile12_node56_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile12_node56_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node56 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,48] 6 (by decide) (choices 2) [3,65,66] profile12_node56_route profile12_node56_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node57
  · exact profile12_node58
  · exact profile12_node59

def profile12_node60_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 53 67 118 122 114 32 64), lower := (rows 53 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 87 67 68 72 80 64 64) }] }

theorem profile12_node60 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,65] 6 114 profile12_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,65] 6 114 profile12_node60_cert).mp (by decide +kernel))

def profile12_node62_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 53 82 7 106 114 32 64), lower := (rows 53 82 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 14 0 127 127), good := (rows 109 106 111 104 96 96 96) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile12_node62 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,3] 6 98 profile12_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,3] 6 98 profile12_node62_cert).mp (by decide +kernel))

def profile12_node63_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 82 37 74 82 32 64), lower := (rows 53 82 37 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 127 127), good := (rows 117 117 101 104 117 96 96) }] }

theorem profile12_node63 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,33] 6 66 profile12_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,33] 6 66 profile12_node63_cert).mp (by decide +kernel))

def profile12_node64_cert : CutBound 7 := { lost := (rows 0 32 16 32 0 0 0), upper := (rows 53 82 38 75 83 32 64), lower := (rows 53 82 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 127 127), good := (rows 101 102 102 104 96 96 96) },{ target := 5, region := (rows 1 19 4 9 17 0 127), good := (rows 95 82 70 72 82 64 64) }] }

theorem profile12_node64 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,34] 6 67 profile12_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,34] 6 67 profile12_node64_cert).mp (by decide +kernel))

def profile12_node65_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 82 69 42 50 32 64), lower := (rows 53 82 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 127 127), good := (rows 117 117 101 104 117 96 96) }] }

theorem profile12_node65 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,65] 6 34 profile12_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,65] 6 34 profile12_node65_cert).mp (by decide +kernel))

def profile12_node66_cert : CutBound 7 := { lost := (rows 0 32 48 0 0 0 0), upper := (rows 53 82 70 43 51 32 64), lower := (rows 53 82 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 127 127), good := (rows 101 102 102 104 96 96 96) },{ target := 5, region := (rows 1 19 23 8 16 0 127), good := (rows 87 86 70 72 86 64 64) }] }

theorem profile12_node66 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,66] 6 35 profile12_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,66] 6 35 profile12_node66_cert).mp (by decide +kernel))

def profile12_node67_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 82 100 11 19 32 64), lower := (rows 53 82 100 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 127 8 16 127 127), good := (rows 117 117 100 108 117 100 100) }] }

theorem profile12_node67 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,96] 6 3 profile12_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80,96] 6 3 profile12_node67_cert).mp (by decide +kernel))

def profile12_node61_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile12_node61_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node61 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,80] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile12_node61_route profile12_node61_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node62
  · exact profile12_node63
  · exact profile12_node64
  · exact profile12_node65
  · exact profile12_node66
  · exact profile12_node67

def profile12_node69_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 53 98 7 90 82 32 64), lower := (rows 53 98 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 5 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile12_node69 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,3] 6 82 profile12_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,3] 6 82 profile12_node69_cert).mp (by decide +kernel))

def profile12_node70_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 98 21 74 82 32 64), lower := (rows 53 98 21 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 21 8 16 127 127), good := (rows 117 96 117 104 117 96 96) }] }

theorem profile12_node70 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,17] 6 66 profile12_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,17] 6 66 profile12_node70_cert).mp (by decide +kernel))

def profile12_node71_cert : CutBound 7 := { lost := (rows 2 16 0 16 0 0 0), upper := (rows 53 98 22 75 83 32 64), lower := (rows 53 98 22 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 117 96 117 104 112 96 96) },{ target := 4, region := (rows 1 127 4 9 0 127 127), good := (rows 111 98 102 106 98 98 98) }] }

theorem profile12_node71 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,18] 6 67 profile12_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,18] 6 67 profile12_node71_cert).mp (by decide +kernel))

def profile12_node72_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 98 69 26 18 32 64), lower := (rows 53 98 69 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 21 8 16 127 127), good := (rows 117 96 101 104 117 96 96) }] }

theorem profile12_node72 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,65] 6 18 profile12_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,65] 6 18 profile12_node72_cert).mp (by decide +kernel))

def profile12_node73_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 53 98 70 27 19 32 64), lower := (rows 53 98 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 127 8 0 127 127), good := (rows 103 102 102 110 102 102 102) }] }

theorem profile12_node73 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,66] 6 19 profile12_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,66] 6 19 profile12_node73_cert).mp (by decide +kernel))

def profile12_node74_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 53 98 84 11 19 32 64), lower := (rows 53 98 84 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 21 8 16 127 127), good := (rows 117 96 117 104 117 96 96) }] }

theorem profile12_node74 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,80] 6 3 profile12_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96,80] 6 3 profile12_node74_cert).mp (by decide +kernel))

def profile12_node68_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile12_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node68 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52,96] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile12_node68_route profile12_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node69
  · exact profile12_node70
  · exact profile12_node71
  · exact profile12_node72
  · exact profile12_node73
  · exact profile12_node74

def profile12_node53_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node53_route : Route 7 := (fun mask => (mask,id))

theorem profile12_node53 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [52] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile12_node53_route profile12_node53_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node54
  · exact profile12_node55
  · exact profile12_node56
  · exact profile12_node60
  · exact profile12_node61
  · exact profile12_node68

def profile12_node76_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 7 118 122 114 32 64), lower := (rows 99 7 4 8 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 127 127), good := (rows 99 103 103 104 96 96 96) }] }

theorem profile12_node76 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,5] 6 114 profile12_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,5] 6 114 profile12_node76_cert).mp (by decide +kernel))

def profile12_node78_cert : CutBound 7 := { lost := (rows 16 0 0 18 0 0 0), upper := (rows 99 19 22 108 116 32 64), lower := (rows 99 19 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 113 124 104 112 96 96) },{ target := 4, region := (rows 7 2 4 12 0 127 127), good := (rows 99 99 111 104 96 96 96) }] }

theorem profile12_node78 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,18] 6 100 profile12_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,18] 6 100 profile12_node78_cert).mp (by decide +kernel))

def profile12_node79_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 99 19 38 92 84 32 64), lower := (rows 99 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 113 124 104 112 96 96) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node79 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,34] 6 84 profile12_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,34] 6 84 profile12_node79_cert).mp (by decide +kernel))

def profile12_node80_cert : CutBound 7 := { lost := (rows 16 0 2 0 0 0 0), upper := (rows 99 19 52 78 86 32 64), lower := (rows 99 19 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 117 116 104 116 96 96) },{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile12_node80 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,48] 6 70 profile12_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,48] 6 70 profile12_node80_cert).mp (by decide +kernel))

def profile12_node81_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 99 19 100 30 22 32 64), lower := (rows 99 19 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 117 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile12_node81 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,96] 6 22 profile12_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17,96] 6 22 profile12_node81_cert).mp (by decide +kernel))

def profile12_node77_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node77_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node77 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,17] 6 (by decide) (choices 2) [18,34,48,96] profile12_node77_route profile12_node77_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node78
  · exact profile12_node79
  · exact profile12_node80
  · exact profile12_node81

def profile12_node83_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 99 22 7 120 112 32 64), lower := (rows 99 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 124 125 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node83 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,3] 6 112 profile12_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,3] 6 112 profile12_node83_cert).mp (by decide +kernel))

def profile12_node84_cert : CutBound 7 := { lost := (rows 16 0 0 16 0 0 0), upper := (rows 99 22 21 106 114 32 64), lower := (rows 99 22 21 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 127 127), good := (rows 107 111 109 104 96 96 96) }] }

theorem profile12_node84 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,17] 6 98 profile12_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,17] 6 98 profile12_node84_cert).mp (by decide +kernel))

def profile12_node85_cert : CutBound 7 := { lost := (rows 16 0 0 18 0 0 0), upper := (rows 99 22 22 105 113 32 64), lower := (rows 99 22 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 116 116 104 112 96 96) },{ target := 4, region := (rows 7 2 4 15 0 127 127), good := (rows 107 111 111 104 96 96 96) }] }

theorem profile12_node85 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,18] 6 97 profile12_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,18] 6 97 profile12_node85_cert).mp (by decide +kernel))

def profile12_node86_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 99 22 37 90 82 32 64), lower := (rows 99 22 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 116 101 104 112 96 96) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile12_node86 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,33] 6 82 profile12_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,33] 6 82 profile12_node86_cert).mp (by decide +kernel))

def profile12_node87_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 99 22 38 89 81 32 64), lower := (rows 99 22 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 116 100 104 112 96 96) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile12_node87 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,34] 6 81 profile12_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,34] 6 81 profile12_node87_cert).mp (by decide +kernel))

def profile12_node88_cert : CutBound 7 := { lost := (rows 16 0 2 16 0 0 0), upper := (rows 99 22 52 75 83 32 64), lower := (rows 99 22 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 116 116 104 116 96 96) },{ target := 4, region := (rows 3 2 4 11 0 127 127), good := (rows 107 111 100 104 96 96 96) }] }

theorem profile12_node88 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,48] 6 67 profile12_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,48] 6 67 profile12_node88_cert).mp (by decide +kernel))

def profile12_node89_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 99 22 100 27 19 32 64), lower := (rows 99 22 100 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 116 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile12_node89 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,96] 6 19 profile12_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20,96] 6 19 profile12_node89_cert).mp (by decide +kernel))

def profile12_node82_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node82_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node82 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,20] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile12_node82_route profile12_node82_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node83
  · exact profile12_node84
  · exact profile12_node85
  · exact profile12_node86
  · exact profile12_node87
  · exact profile12_node88
  · exact profile12_node89

def profile12_node90_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 35 86 94 86 32 64), lower := (rows 99 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) }] }

theorem profile12_node90 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,33] 6 86 profile12_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,33] 6 86 profile12_node90_cert).mp (by decide +kernel))

def profile12_node91_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 38 87 91 83 32 64), lower := (rows 99 38 4 8 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 127 127), good := (rows 99 103 103 104 96 96 96) }] }

theorem profile12_node91 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,36] 6 83 profile12_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,36] 6 83 profile12_node91_cert).mp (by decide +kernel))

def profile12_node92_cert : CutBound 7 := { lost := (rows 16 0 32 32 0 0 0), upper := (rows 99 50 87 95 87 32 64), lower := (rows 99 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile12_node92 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,48] 6 87 profile12_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,48] 6 87 profile12_node92_cert).mp (by decide +kernel))

def profile12_node93_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 98 23 31 23 32 64), lower := (rows 99 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) }] }

theorem profile12_node93 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,96] 6 23 profile12_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98,96] 6 23 profile12_node93_cert).mp (by decide +kernel))

def profile12_node75_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node75_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node75 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [98] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile12_node75_route profile12_node75_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node76
  · exact profile12_node77
  · exact profile12_node82
  · exact profile12_node90
  · exact profile12_node91
  · exact profile12_node92
  · exact profile12_node93

def profile12_node94_cert : CutBound 7 := { lost := (rows 18 0 0 0 0 0 0), upper := (rows 101 115 119 123 115 32 64), lower := (rows 101 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 4, region := (rows 5 2 4 8 0 127 127), good := (rows 101 98 101 104 96 96 96) }] }

theorem profile12_node94 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [100] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [100] 6 115 profile12_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [100] 6 115 profile12_node94_cert).mp (by decide +kernel))

def profile12_node97_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 113 7 22 106 114 32 64), lower := (rows 113 7 22 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 8 16 127 127), good := (rows 113 101 117 104 113 96 96) },{ target := 4, region := (rows 1 2 4 14 0 127 127), good := (rows 97 111 110 104 96 96 96) }] }

theorem profile12_node97 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,18] 6 98 profile12_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,18] 6 98 profile12_node97_cert).mp (by decide +kernel))

def profile12_node98_cert : CutBound 7 := { lost := (rows 2 16 16 0 0 0 0), upper := (rows 113 7 38 90 82 32 64), lower := (rows 113 7 38 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 101 100 104 113 96 96) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile12_node98 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,34] 6 82 profile12_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,34] 6 82 profile12_node98_cert).mp (by decide +kernel))

def profile12_node99_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 113 7 52 74 82 32 64), lower := (rows 113 7 52 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 21 8 16 127 127), good := (rows 117 101 117 104 117 96 96) }] }

theorem profile12_node99 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,48] 6 66 profile12_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,48] 6 66 profile12_node99_cert).mp (by decide +kernel))

def profile12_node100_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 113 7 100 26 18 32 64), lower := (rows 113 7 100 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 127 8 16 127 127), good := (rows 117 101 100 108 117 100 100) }] }

theorem profile12_node100 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,96] 6 18 profile12_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5,96] 6 18 profile12_node100_cert).mp (by decide +kernel))

def profile12_node96_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node96_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node96 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,5] 6 (by decide) (choices 2) [18,34,48,96] profile12_node96_route profile12_node96_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node97
  · exact profile12_node98
  · exact profile12_node99
  · exact profile12_node100

def profile12_node101_cert : CutBound 7 := { lost := (rows 2 0 16 16 0 0 0), upper := (rows 113 19 102 110 118 32 64), lower := (rows 113 19 4 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 113 100 104 113 96 96) },{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile12_node101 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,17] 6 102 profile12_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,17] 6 102 profile12_node101_cert).mp (by decide +kernel))

def profile12_node103_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 113 22 7 106 114 32 64), lower := (rows 113 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 117 101 104 113 96 96) },{ target := 4, region := (rows 1 2 4 14 0 127 127), good := (rows 97 110 111 104 96 96 96) }] }

theorem profile12_node103 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,3] 6 98 profile12_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,3] 6 98 profile12_node103_cert).mp (by decide +kernel))

def profile12_node104_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 113 22 37 74 82 32 64), lower := (rows 113 22 37 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 127 127), good := (rows 117 117 101 104 117 96 96) }] }

theorem profile12_node104 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,33] 6 66 profile12_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,33] 6 66 profile12_node104_cert).mp (by decide +kernel))

def profile12_node105_cert : CutBound 7 := { lost := (rows 2 0 16 0 0 0 0), upper := (rows 113 22 38 75 83 32 64), lower := (rows 113 22 38 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 117 101 104 113 96 96) },{ target := 4, region := (rows 1 2 6 8 0 127 127), good := (rows 97 102 102 104 96 96 96) }] }

theorem profile12_node105 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,34] 6 67 profile12_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,34] 6 67 profile12_node105_cert).mp (by decide +kernel))

def profile12_node106_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 113 22 100 11 19 32 64), lower := (rows 113 22 100 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 127 8 16 127 127), good := (rows 117 117 100 108 117 100 100) }] }

theorem profile12_node106 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,96] 6 3 profile12_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20,96] 6 3 profile12_node106_cert).mp (by decide +kernel))

def profile12_node102_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile12_node102_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node102 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,20] 6 (by decide) (choices 2) [3,33,34,96] profile12_node102_route profile12_node102_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node103
  · exact profile12_node104
  · exact profile12_node105
  · exact profile12_node106

def profile12_node107_cert : CutBound 7 := { lost := (rows 2 16 0 0 0 0 0), upper := (rows 113 35 86 94 86 32 64), lower := (rows 113 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 97 100 104 113 96 96) },{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile12_node107 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,33] 6 86 profile12_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,33] 6 86 profile12_node107_cert).mp (by decide +kernel))

def profile12_node108_cert : CutBound 7 := { lost := (rows 2 16 0 0 0 0 0), upper := (rows 113 38 87 91 83 32 64), lower := (rows 113 38 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 100 100 104 113 96 96) },{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 97 102 102 104 96 96 96) }] }

theorem profile12_node108 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,36] 6 83 profile12_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,36] 6 83 profile12_node108_cert).mp (by decide +kernel))

def profile12_node109_cert : CutBound 7 := { lost := (rows 2 64 0 0 0 0 0), upper := (rows 113 50 71 79 87 32 64), lower := (rows 113 50 4 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 113 100 104 113 96 96) },{ target := 6, region := (rows 1 19 4 8 16 127 0), good := (rows 51 50 36 40 50 32 32) }] }

theorem profile12_node109 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,48] 6 71 profile12_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,48] 6 71 profile12_node109_cert).mp (by decide +kernel))

def profile12_node110_cert : CutBound 7 := { lost := (rows 2 16 0 0 0 0 0), upper := (rows 113 98 23 31 23 32 64), lower := (rows 113 98 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 96 100 104 113 96 96) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile12_node110 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,96] 6 23 profile12_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112,96] 6 23 profile12_node110_cert).mp (by decide +kernel))

def profile12_node95_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile12_node95_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node95 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [112] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile12_node95_route profile12_node95_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node96
  · exact profile12_node101
  · exact profile12_node102
  · exact profile12_node107
  · exact profile12_node108
  · exact profile12_node109
  · exact profile12_node110

def profile12_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile12_node0_route : Route 7 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node0 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [] 6 (by decide) (choices 3) [22,38,50,52,98,100,112] profile12_node0_route profile12_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node1
  · exact profile12_node13
  · exact profile12_node36
  · exact profile12_node53
  · exact profile12_node75
  · exact profile12_node94
  · exact profile12_node95

theorem profile12 : Upper (D (n:=7) [49,34,33,32,18,2,2]) (R (n:=7) [49,34,33,32,18,2,2]) [] 6 := profile12_node0


#print axioms profile12
end Delivery.SmallBudgetTenFinite7
