import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile20_node3_cert : CutBound 7 := { lost := (rows 64 64 64 0 0 0 0), upper := (rows 7 11 37 105 113 32 64), lower := (rows 7 11 37 8 16 32 64), losses := [{ target := 6, region := (rows 11 10 15 8 16 127 0), good := (rows 39 47 37 47 48 32 32) }] }

theorem profile20_node3 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,33] 6 97 profile20_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,33] 6 97 profile20_node3_cert).mp (by decide +kernel))

def profile20_node4_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 7 11 100 105 113 32 64), lower := (rows 7 11 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 110 100 108 116 100 100) }] }

theorem profile20_node4 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,96] 6 97 profile20_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9,96] 6 97 profile20_node4_cert).mp (by decide +kernel))

def profile20_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node2_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node2 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,9] 6 (by decide) (choices 2) [33,96] profile20_node2_route profile20_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node3
  · exact profile20_node4

def profile20_node5_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 7 35 109 105 121 32 64), lower := (rows 7 35 4 8 16 32 64), losses := [{ target := 6, region := (rows 5 7 4 8 16 127 0), good := (rows 39 35 39 40 48 32 32) }] }

theorem profile20_node5 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,33] 6 105 profile20_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,33] 6 105 profile20_node5_cert).mp (by decide +kernel))

def profile20_node6_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 42 101 105 113 32 64), lower := (rows 7 42 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 102 106 100 106 112 96 96) }] }

theorem profile20_node6 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,40] 6 97 profile20_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,40] 6 97 profile20_node6_cert).mp (by decide +kernel))

def profile20_node7_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 7 98 109 105 121 32 64), lower := (rows 7 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) }] }

theorem profile20_node7 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,96] 6 105 profile20_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6,96] 6 105 profile20_node7_cert).mp (by decide +kernel))

def profile20_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node1 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [6] 6 (by decide) (choices 2) [9,33,40,96] profile20_node1_route profile20_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node2
  · exact profile20_node5
  · exact profile20_node6
  · exact profile20_node7

def profile20_node8_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 35 111 109 109 125 32 64), lower := (rows 35 2 4 8 16 32 64), losses := [{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 36 40 48 32 32) }] }

theorem profile20_node8 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [34] 6 109 profile20_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [34] 6 109 profile20_node8_cert).mp (by decide +kernel))

def profile20_node11_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 97 7 7 105 121 32 64), lower := (rows 97 7 7 8 16 32 64), losses := [{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile20_node11 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,3] 6 105 profile20_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,3] 6 105 profile20_node11_cert).mp (by decide +kernel))

def profile20_node12_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 97 7 13 107 115 32 64), lower := (rows 97 7 13 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 65 71 79 72 80 64 64) }] }

theorem profile20_node12 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,9] 6 99 profile20_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,9] 6 99 profile20_node12_cert).mp (by decide +kernel))

def profile20_node14_cert : CutBound 7 := { lost := (rows 0 32 32 0 32 0 0), upper := (rows 97 7 14 41 81 32 64), lower := (rows 97 7 14 41 16 32 64), losses := [{ target := 5, region := (rows 1 10 12 8 27 0 127), good := (rows 81 87 94 95 80 64 64) }] }

theorem profile20_node14 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,33] 6 65 profile20_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,33] 6 65 profile20_node14_cert).mp (by decide +kernel))

def profile20_node15_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 97 7 14 104 17 32 64), lower := (rows 97 7 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 127 16 127 127), good := (rows 104 110 110 104 120 104 104) }] }

theorem profile20_node15 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,96] 6 1 profile20_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10,96] 6 1 profile20_node15_cert).mp (by decide +kernel))

def profile20_node13_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node13_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node13 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,10] 6 (by decide) (choices 2) [33,96] profile20_node13_route profile20_node13_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node14
  · exact profile20_node15

def profile20_node16_cert : CutBound 7 := { lost := (rows 0 32 0 32 32 0 0), upper := (rows 97 7 37 75 91 32 64), lower := (rows 97 7 37 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 14 22 0 127), good := (rows 65 95 95 72 80 64 64) }] }

theorem profile20_node16 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,33] 6 75 profile20_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,33] 6 75 profile20_node16_cert).mp (by decide +kernel))

def profile20_node17_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 97 7 38 73 89 32 64), lower := (rows 97 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 96 102 102 104 112 96 96) }] }

theorem profile20_node17 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,34] 6 73 profile20_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,34] 6 73 profile20_node17_cert).mp (by decide +kernel))

def profile20_node18_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 97 7 44 75 83 32 64), lower := (rows 97 7 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 96 102 108 108 112 96 96) }] }

theorem profile20_node18 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,40] 6 67 profile20_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,40] 6 67 profile20_node18_cert).mp (by decide +kernel))

def profile20_node19_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 97 7 100 11 27 32 64), lower := (rows 97 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) }] }

theorem profile20_node19 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,96] 6 11 profile20_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5,96] 6 11 profile20_node19_cert).mp (by decide +kernel))

def profile20_node10_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node10_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node10 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,5] 6 (by decide) (choices 2) [3,9,10,33,34,40,96] profile20_node10_route profile20_node10_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile20_node11
  · exact profile20_node12
  · exact profile20_node13
  · exact profile20_node16
  · exact profile20_node17
  · exact profile20_node18
  · exact profile20_node19

def profile20_node22_cert : CutBound 7 := { lost := (rows 0 32 32 0 32 0 0), upper := (rows 97 14 7 41 81 32 64), lower := (rows 97 14 7 41 16 32 64), losses := [{ target := 5, region := (rows 1 10 12 8 29 0 127), good := (rows 81 94 87 95 80 64 64) }] }

theorem profile20_node22 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,33] 6 65 profile20_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,33] 6 65 profile20_node22_cert).mp (by decide +kernel))

def profile20_node23_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 14 7 104 17 32 64), lower := (rows 97 14 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 104 110 110 104 120 104 104) }] }

theorem profile20_node23 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,96] 6 1 profile20_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3,96] 6 1 profile20_node23_cert).mp (by decide +kernel))

def profile20_node21_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node21_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node21 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,3] 6 (by decide) (choices 2) [33,96] profile20_node21_route profile20_node21_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile20_node22
  · exact profile20_node23

def profile20_node24_cert : CutBound 7 := { lost := (rows 0 32 0 32 32 0 0), upper := (rows 97 14 37 75 83 32 64), lower := (rows 97 14 37 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 65 94 95 72 80 64 64) }] }

theorem profile20_node24 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,33] 6 67 profile20_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,33] 6 67 profile20_node24_cert).mp (by decide +kernel))

def profile20_node25_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 97 14 38 73 81 32 64), lower := (rows 97 14 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 14 8 16 127 127), good := (rows 96 110 102 110 112 96 96) }] }

theorem profile20_node25 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,34] 6 65 profile20_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,34] 6 65 profile20_node25_cert).mp (by decide +kernel))

def profile20_node26_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 97 14 100 11 19 32 64), lower := (rows 97 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 100 110 100 110 116 100 100) }] }

theorem profile20_node26 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,96] 6 3 profile20_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12,96] 6 3 profile20_node26_cert).mp (by decide +kernel))

def profile20_node20_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node20_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node20 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,12] 6 (by decide) (choices 2) [3,33,34,96] profile20_node20_route profile20_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node21
  · exact profile20_node24
  · exact profile20_node25
  · exact profile20_node26

def profile20_node27_cert : CutBound 7 := { lost := (rows 0 0 32 32 32 0 0), upper := (rows 97 35 79 79 95 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile20_node27 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,33] 6 79 profile20_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,33] 6 79 profile20_node27_cert).mp (by decide +kernel))

def profile20_node28_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 97 38 79 75 91 32 64), lower := (rows 97 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) }] }

theorem profile20_node28 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,36] 6 75 profile20_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,36] 6 75 profile20_node28_cert).mp (by decide +kernel))

def profile20_node29_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 97 98 15 15 31 32 64), lower := (rows 97 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) }] }

theorem profile20_node29 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,96] 6 15 profile20_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96,96] 6 15 profile20_node29_cert).mp (by decide +kernel))

def profile20_node9_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node9_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node9 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [96] 6 (by decide) (choices 2) [5,12,33,36,96] profile20_node9_route profile20_node9_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile20_node10
  · exact profile20_node20
  · exact profile20_node27
  · exact profile20_node28
  · exact profile20_node29

def profile20_node0_column : Nat → Fin 7 := fun mask => match mask with | 18 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile20_node0_route : Route 7 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 72 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile20_node0 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [] 6 (by decide) (choices 2) [6,34,96] profile20_node0_route profile20_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node1
  · exact profile20_node8
  · exact profile20_node9

theorem profile20 : Upper (D (n:=7) [35,33,33,33,32,2,2]) (R (n:=7) [35,33,33,33,32,2,2]) [] 6 := profile20_node0


#print axioms profile20
end Delivery.SmallBudgetTenFinite7
