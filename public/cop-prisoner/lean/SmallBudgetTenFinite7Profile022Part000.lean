import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile22_node3_cert : CutBound 7 := { lost := (rows 0 0 0 1 1 0 0), upper := (rows 7 11 21 104 112 32 64), lower := (rows 7 11 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile22_node3 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,17] 6 96 profile22_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,17] 6 96 profile22_node3_cert).mp (by decide +kernel))

def profile22_node4_cert : CutBound 7 := { lost := (rows 0 0 0 1 1 0 0), upper := (rows 7 11 37 120 112 32 64), lower := (rows 7 11 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) }] }

theorem profile22_node4 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,33] 6 112 profile22_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,33] 6 112 profile22_node4_cert).mp (by decide +kernel))

def profile22_node5_cert : CutBound 7 := { lost := (rows 0 0 65 0 0 0 0), upper := (rows 7 11 52 105 113 32 64), lower := (rows 7 11 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 127 127), good := (rows 102 106 116 104 116 96 96) },{ target := 6, region := (rows 1 2 20 8 16 127 0), good := (rows 39 43 52 40 52 32 32) }] }

theorem profile22_node5 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,48] 6 97 profile22_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,48] 6 97 profile22_node5_cert).mp (by decide +kernel))

def profile22_node7_cert : CutBound 7 := { lost := (rows 0 0 1 0 1 0 0), upper := (rows 7 11 100 25 112 32 64), lower := (rows 7 11 100 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 126 116 124 116 116 116) }] }

theorem profile22_node7 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,17] 6 96 profile22_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,17] 6 96 profile22_node7_cert).mp (by decide +kernel))

def profile22_node8_cert : CutBound 7 := { lost := (rows 0 0 1 0 1 0 0), upper := (rows 7 11 100 41 80 32 64), lower := (rows 7 11 100 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 126 116 124 116 116 116) }] }

theorem profile22_node8 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,33] 6 80 profile22_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,33] 6 80 profile22_node8_cert).mp (by decide +kernel))

def profile22_node9_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 7 11 100 56 81 32 64), lower := (rows 7 11 100 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 24 16 127 127), good := (rows 102 110 100 124 124 100 100) }] }

theorem profile22_node9 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,48] 6 65 profile22_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,48] 6 65 profile22_node9_cert).mp (by decide +kernel))

def profile22_node10_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 7 11 100 104 17 32 64), lower := (rows 7 11 100 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 127 16 127 127), good := (rows 110 110 108 108 124 108 108) }] }

theorem profile22_node10 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,96] 6 17 profile22_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96,96] 6 17 profile22_node10_cert).mp (by decide +kernel))

def profile22_node6_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile22_node6_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node6 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9,96] 6 (by decide) (choices 2) [17,33,48,96] profile22_node6_route profile22_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node7
  · exact profile22_node8
  · exact profile22_node9
  · exact profile22_node10

def profile22_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile22_node2_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node2 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,9] 6 (by decide) (choices 2) [17,33,48,96] profile22_node2_route profile22_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node3
  · exact profile22_node4
  · exact profile22_node5
  · exact profile22_node6

def profile22_node12_cert : CutBound 7 := { lost := (rows 64 0 64 0 0 0 0), upper := (rows 7 26 37 105 113 32 64), lower := (rows 7 26 37 8 16 32 64), losses := [{ target := 6, region := (rows 3 2 7 8 16 127 0), good := (rows 39 63 37 40 48 32 32) }] }

theorem profile22_node12 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,33] 6 97 profile22_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,33] 6 97 profile22_node12_cert).mp (by decide +kernel))

def profile22_node14_cert : CutBound 7 := { lost := (rows 0 32 1 0 32 0 0), upper := (rows 7 26 100 41 81 32 64), lower := (rows 7 26 100 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 126 100 108 116 100 100) },{ target := 5, region := (rows 1 10 4 8 25 0 127), good := (rows 87 90 68 91 80 64 64) }] }

theorem profile22_node14 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,33] 6 65 profile22_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,33] 6 65 profile22_node14_cert).mp (by decide +kernel))

def profile22_node15_cert : CutBound 7 := { lost := (rows 0 1 1 1 0 0 0), upper := (rows 7 26 100 104 17 32 64), lower := (rows 7 26 100 104 16 32 64), losses := [{ target := 0, region := (rows 0 18 127 127 16 127 127), good := (rows 110 126 108 108 126 108 108) }] }

theorem profile22_node15 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,96] 6 1 profile22_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96,96] 6 1 profile22_node15_cert).mp (by decide +kernel))

def profile22_node13_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node13_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node13 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24,96] 6 (by decide) (choices 2) [33,96] profile22_node13_route profile22_node13_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node14
  · exact profile22_node15

def profile22_node11_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node11_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node11 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,24] 6 (by decide) (choices 2) [33,96] profile22_node11_route profile22_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node12
  · exact profile22_node13

def profile22_node16_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 7 35 125 121 121 32 64), lower := (rows 7 35 4 8 16 32 64), losses := [{ target := 6, region := (rows 5 7 4 8 16 127 0), good := (rows 39 35 39 40 48 32 32) }] }

theorem profile22_node16 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,33] 6 121 profile22_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,33] 6 121 profile22_node16_cert).mp (by decide +kernel))

def profile22_node17_cert : CutBound 7 := { lost := (rows 0 65 0 0 0 0 0), upper := (rows 7 42 117 121 113 32 64), lower := (rows 7 42 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 102 106 100 106 112 96 96) },{ target := 6, region := (rows 1 10 4 8 16 127 0), good := (rows 39 42 36 42 48 32 32) }] }

theorem profile22_node17 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,40] 6 113 profile22_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,40] 6 113 profile22_node17_cert).mp (by decide +kernel))

def profile22_node20_cert : CutBound 7 := { lost := (rows 0 1 0 0 1 0 0), upper := (rows 7 98 13 25 112 32 64), lower := (rows 7 98 13 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) }] }

theorem profile22_node20 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,17] 6 96 profile22_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,17] 6 96 profile22_node20_cert).mp (by decide +kernel))

def profile22_node21_cert : CutBound 7 := { lost := (rows 0 1 0 0 1 0 0), upper := (rows 7 98 13 41 80 32 64), lower := (rows 7 98 13 41 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) }] }

theorem profile22_node21 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,33] 6 80 profile22_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,33] 6 80 profile22_node21_cert).mp (by decide +kernel))

def profile22_node22_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 98 13 56 81 32 64), lower := (rows 7 98 13 56 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 24 16 127 127), good := (rows 102 98 110 122 122 98 98) }] }

theorem profile22_node22 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,48] 6 65 profile22_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,48] 6 65 profile22_node22_cert).mp (by decide +kernel))

def profile22_node23_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 7 98 13 104 17 32 64), lower := (rows 7 98 13 104 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 127), good := (rows 110 106 110 106 122 106 106) }] }

theorem profile22_node23 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,96] 6 17 profile22_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9,96] 6 17 profile22_node23_cert).mp (by decide +kernel))

def profile22_node19_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile22_node19_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node19 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,9] 6 (by decide) (choices 2) [17,33,48,96] profile22_node19_route profile22_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node20
  · exact profile22_node21
  · exact profile22_node22
  · exact profile22_node23

def profile22_node25_cert : CutBound 7 := { lost := (rows 0 1 32 0 32 0 0), upper := (rows 7 98 28 41 81 32 64), lower := (rows 7 98 28 41 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 126 106 114 98 98) },{ target := 5, region := (rows 1 2 12 8 25 0 127), good := (rows 87 66 92 93 80 64 64) }] }

theorem profile22_node25 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,33] 6 65 profile22_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,33] 6 65 profile22_node25_cert).mp (by decide +kernel))

def profile22_node26_cert : CutBound 7 := { lost := (rows 0 1 1 1 0 0 0), upper := (rows 7 98 28 104 17 32 64), lower := (rows 7 98 28 104 16 32 64), losses := [{ target := 0, region := (rows 0 127 20 127 16 127 127), good := (rows 110 106 126 106 126 106 106) }] }

theorem profile22_node26 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,96] 6 1 profile22_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24,96] 6 1 profile22_node26_cert).mp (by decide +kernel))

def profile22_node24_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node24_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node24 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,24] 6 (by decide) (choices 2) [33,96] profile22_node24_route profile22_node24_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node25
  · exact profile22_node26

def profile22_node27_cert : CutBound 7 := { lost := (rows 0 1 0 32 32 0 0), upper := (rows 7 98 37 89 89 32 64), lower := (rows 7 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 4 13 21 0 127), good := (rows 95 66 93 72 80 64 64) }] }

theorem profile22_node27 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,33] 6 89 profile22_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,33] 6 89 profile22_node27_cert).mp (by decide +kernel))

def profile22_node28_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 98 44 89 81 32 64), lower := (rows 7 98 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 102 98 110 110 114 98 98) }] }

theorem profile22_node28 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,40] 6 81 profile22_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,40] 6 81 profile22_node28_cert).mp (by decide +kernel))

def profile22_node29_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 7 98 100 25 25 32 64), lower := (rows 7 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) }] }

theorem profile22_node29 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,96] 6 25 profile22_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96,96] 6 25 profile22_node29_cert).mp (by decide +kernel))

def profile22_node18_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile22_node18_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node18 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6,96] 6 (by decide) (choices 2) [9,24,33,40,96] profile22_node18_route profile22_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile22_node19
  · exact profile22_node24
  · exact profile22_node27
  · exact profile22_node28
  · exact profile22_node29

def profile22_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile22_node1_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node1 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [6] 6 (by decide) (choices 2) [9,24,33,40,96] profile22_node1_route profile22_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile22_node2
  · exact profile22_node11
  · exact profile22_node16
  · exact profile22_node17
  · exact profile22_node18

def profile22_node31_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 35 7 125 121 121 32 64), lower := (rows 35 7 4 8 16 32 64), losses := [{ target := 6, region := (rows 7 6 4 8 16 127 0), good := (rows 35 39 39 40 48 32 32) }] }

theorem profile22_node31 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,5] 6 121 profile22_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,5] 6 121 profile22_node31_cert).mp (by decide +kernel))

def profile22_node34_cert : CutBound 7 := { lost := (rows 0 32 32 0 33 0 0), upper := (rows 35 14 21 41 80 32 64), lower := (rows 35 14 21 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 114 126 116 120 112 112 112) },{ target := 5, region := (rows 1 10 13 8 127 0 127), good := (rows 87 94 85 95 80 80 80) }] }

theorem profile22_node34 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,33] 6 64 profile22_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,33] 6 64 profile22_node34_cert).mp (by decide +kernel))

def profile22_node35_cert : CutBound 7 := { lost := (rows 0 32 0 32 1 0 0), upper := (rows 35 14 21 73 112 32 64), lower := (rows 35 14 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 114 126 116 120 112 112 112) },{ target := 5, region := (rows 1 6 4 13 16 0 127), good := (rows 75 78 95 73 80 64 64) }] }

theorem profile22_node35 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,65] 6 96 profile22_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,65] 6 96 profile22_node35_cert).mp (by decide +kernel))

def profile22_node36_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 35 14 21 104 81 32 64), lower := (rows 35 14 21 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 106 110 126 104 120 104 104) }] }

theorem profile22_node36 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,96] 6 65 profile22_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17,96] 6 65 profile22_node36_cert).mp (by decide +kernel))

def profile22_node33_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node33 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,17] 6 (by decide) (choices 2) [33,65,96] profile22_node33_route profile22_node33_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node34
  · exact profile22_node35
  · exact profile22_node36

def profile22_node37_cert : CutBound 7 := { lost := (rows 0 32 0 32 32 0 0), upper := (rows 35 14 37 89 81 32 64), lower := (rows 35 14 37 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 13 21 0 127), good := (rows 91 94 95 72 80 64 64) }] }

theorem profile22_node37 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,33] 6 81 profile22_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,33] 6 81 profile22_node37_cert).mp (by decide +kernel))

def profile22_node38_cert : CutBound 7 := { lost := (rows 0 0 1 32 32 0 0), upper := (rows 35 14 52 73 81 32 64), lower := (rows 35 14 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 127 127), good := (rows 98 110 116 104 116 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 91 78 84 72 80 64 64) }] }

theorem profile22_node38 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,48] 6 65 profile22_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,48] 6 65 profile22_node38_cert).mp (by decide +kernel))

def profile22_node39_cert : CutBound 7 := { lost := (rows 64 0 32 0 0 0 0), upper := (rows 35 14 69 121 113 32 64), lower := (rows 35 14 69 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 71 78 69 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 47 37 40 48 32 32) }] }

theorem profile22_node39 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,65] 6 113 profile22_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,65] 6 113 profile22_node39_cert).mp (by decide +kernel))

def profile22_node40_cert : CutBound 7 := { lost := (rows 0 0 33 0 0 0 0), upper := (rows 35 14 84 105 113 32 64), lower := (rows 35 14 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 127 127), good := (rows 98 110 116 104 116 96 96) },{ target := 5, region := (rows 1 2 20 8 16 0 127), good := (rows 67 78 84 72 84 64 64) }] }

theorem profile22_node40 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,80] 6 97 profile22_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,80] 6 97 profile22_node40_cert).mp (by decide +kernel))

def profile22_node41_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 14 100 89 81 32 64), lower := (rows 35 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 102 110 100 110 116 100 100) }] }

theorem profile22_node41 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,96] 6 81 profile22_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12,96] 6 81 profile22_node41_cert).mp (by decide +kernel))

def profile22_node32_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile22_node32_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node32 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,12] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile22_node32_route profile22_node32_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node33
  · exact profile22_node37
  · exact profile22_node38
  · exact profile22_node39
  · exact profile22_node40
  · exact profile22_node41

def profile22_node42_cert : CutBound 7 := { lost := (rows 0 0 32 32 32 0 0), upper := (rows 35 35 93 93 93 32 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile22_node42 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,33] 6 93 profile22_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,33] 6 93 profile22_node42_cert).mp (by decide +kernel))

def profile22_node43_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 38 93 89 89 32 64), lower := (rows 35 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) }] }

theorem profile22_node43 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,36] 6 89 profile22_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,36] 6 89 profile22_node43_cert).mp (by decide +kernel))

def profile22_node44_cert : CutBound 7 := { lost := (rows 64 32 0 0 0 0 0), upper := (rows 35 67 125 125 125 32 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 36 40 48 32 32) }] }

theorem profile22_node44 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,65] 6 125 profile22_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,65] 6 125 profile22_node44_cert).mp (by decide +kernel))

def profile22_node45_cert : CutBound 7 := { lost := (rows 0 33 0 0 0 0 0), upper := (rows 35 70 125 121 121 32 64), lower := (rows 35 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 70 70 72 80 64 64) }] }

theorem profile22_node45 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,68] 6 121 profile22_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,68] 6 121 profile22_node45_cert).mp (by decide +kernel))

def profile22_node46_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 98 93 93 93 32 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile22_node46 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,96] 6 93 profile22_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34,96] 6 93 profile22_node46_cert).mp (by decide +kernel))

def profile22_node30_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile22_node30_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile22_node30 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [34] 6 (by decide) (choices 2) [5,12,33,36,65,68,96] profile22_node30_route profile22_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node31
  · exact profile22_node32
  · exact profile22_node42
  · exact profile22_node43
  · exact profile22_node44
  · exact profile22_node45
  · exact profile22_node46

def profile22_node49_cert : CutBound 7 := { lost := (rows 0 0 0 1 1 0 0), upper := (rows 97 7 7 120 120 32 64), lower := (rows 97 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) }] }

theorem profile22_node49 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,3] 6 120 profile22_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,3] 6 120 profile22_node49_cert).mp (by decide +kernel))

def profile22_node50_cert : CutBound 7 := { lost := (rows 0 0 0 1 1 0 0), upper := (rows 97 7 13 122 114 32 64), lower := (rows 97 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 96 126 108 104 112 96 96) }] }

theorem profile22_node50 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,9] 6 114 profile22_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,9] 6 114 profile22_node50_cert).mp (by decide +kernel))

def profile22_node52_cert : CutBound 7 := { lost := (rows 0 32 32 0 1 0 0), upper := (rows 97 7 14 25 112 32 64), lower := (rows 97 7 14 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 118 126 120 112 112 112) },{ target := 5, region := (rows 1 10 12 8 16 0 127), good := (rows 65 71 78 95 80 64 64) }] }

theorem profile22_node52 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,17] 6 96 profile22_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,17] 6 96 profile22_node52_cert).mp (by decide +kernel))

def profile22_node53_cert : CutBound 7 := { lost := (rows 0 32 32 0 33 0 0), upper := (rows 97 7 14 41 80 32 64), lower := (rows 97 7 14 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 118 126 120 112 112 112) },{ target := 5, region := (rows 1 10 12 8 127 0 127), good := (rows 81 87 94 95 80 80 80) }] }

theorem profile22_node53 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,33] 6 80 profile22_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,33] 6 80 profile22_node53_cert).mp (by decide +kernel))

def profile22_node54_cert : CutBound 7 := { lost := (rows 0 0 0 1 32 0 0), upper := (rows 97 7 14 56 81 32 64), lower := (rows 97 7 14 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 24 16 127 127), good := (rows 96 102 110 120 120 96 96) },{ target := 5, region := (rows 1 2 4 8 19 0 127), good := (rows 81 87 94 88 80 64 64) }] }

theorem profile22_node54 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,48] 6 65 profile22_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,48] 6 65 profile22_node54_cert).mp (by decide +kernel))

def profile22_node55_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 97 7 14 104 17 32 64), lower := (rows 97 7 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 127 16 127 127), good := (rows 104 110 110 104 120 104 104) }] }

theorem profile22_node55 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,96] 6 17 profile22_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10,96] 6 17 profile22_node55_cert).mp (by decide +kernel))

def profile22_node51_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile22_node51_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node51 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,10] 6 (by decide) (choices 2) [17,33,48,96] profile22_node51_route profile22_node51_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node52
  · exact profile22_node53
  · exact profile22_node54
  · exact profile22_node55

def profile22_node57_cert : CutBound 7 := { lost := (rows 0 0 1 0 1 0 0), upper := (rows 97 7 28 11 112 32 64), lower := (rows 97 7 28 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 112 118 124 126 112 112 112) }] }

theorem profile22_node57 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,3] 6 96 profile22_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,3] 6 96 profile22_node57_cert).mp (by decide +kernel))

def profile22_node58_cert : CutBound 7 := { lost := (rows 0 32 32 0 33 0 0), upper := (rows 97 7 28 41 82 32 64), lower := (rows 97 7 28 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 18 127 127), good := (rows 96 118 124 104 112 96 96) },{ target := 5, region := (rows 1 10 12 8 30 0 127), good := (rows 65 87 94 95 80 64 64) }] }

theorem profile22_node58 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,33] 6 66 profile22_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,33] 6 66 profile22_node58_cert).mp (by decide +kernel))

def profile22_node59_cert : CutBound 7 := { lost := (rows 0 0 32 1 32 0 0), upper := (rows 97 7 28 42 81 32 64), lower := (rows 97 7 28 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 127 127), good := (rows 96 110 124 106 112 96 96) },{ target := 5, region := (rows 1 2 12 8 19 0 127), good := (rows 81 87 92 94 80 64 64) }] }

theorem profile22_node59 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,34] 6 65 profile22_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,34] 6 65 profile22_node59_cert).mp (by decide +kernel))

def profile22_node60_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 97 7 28 104 19 32 64), lower := (rows 97 7 28 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 127 16 127 127), good := (rows 104 110 124 104 124 104 104) }] }

theorem profile22_node60 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,96] 6 3 profile22_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24,96] 6 3 profile22_node60_cert).mp (by decide +kernel))

def profile22_node56_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node56_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node56 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,24] 6 (by decide) (choices 2) [3,33,34,96] profile22_node56_route profile22_node56_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node57
  · exact profile22_node58
  · exact profile22_node59
  · exact profile22_node60

def profile22_node61_cert : CutBound 7 := { lost := (rows 0 0 0 1 1 0 0), upper := (rows 97 7 37 90 90 32 64), lower := (rows 97 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 96 126 100 104 112 96 96) }] }

theorem profile22_node61 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,33] 6 90 profile22_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,33] 6 90 profile22_node61_cert).mp (by decide +kernel))

def profile22_node62_cert : CutBound 7 := { lost := (rows 0 0 1 32 32 0 0), upper := (rows 97 7 38 89 89 32 64), lower := (rows 97 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 89 95 94 72 80 64 64) }] }

theorem profile22_node62 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,34] 6 89 profile22_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,34] 6 89 profile22_node62_cert).mp (by decide +kernel))

def profile22_node63_cert : CutBound 7 := { lost := (rows 0 0 1 32 32 0 0), upper := (rows 97 7 44 91 83 32 64), lower := (rows 97 7 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 96 102 108 108 112 96 96) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 76 72 80 64 64) }] }

theorem profile22_node63 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,40] 6 83 profile22_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,40] 6 83 profile22_node63_cert).mp (by decide +kernel))

def profile22_node64_cert : CutBound 7 := { lost := (rows 0 0 1 32 32 0 0), upper := (rows 97 7 100 27 27 32 64), lower := (rows 97 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile22_node64 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,96] 6 27 profile22_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5,96] 6 27 profile22_node64_cert).mp (by decide +kernel))

def profile22_node48_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile22_node48_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node48 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,5] 6 (by decide) (choices 2) [3,9,10,24,33,34,40,96] profile22_node48_route profile22_node48_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node49
  · exact profile22_node50
  · exact profile22_node51
  · exact profile22_node56
  · exact profile22_node61
  · exact profile22_node62
  · exact profile22_node63
  · exact profile22_node64

def profile22_node67_cert : CutBound 7 := { lost := (rows 0 32 32 0 1 0 0), upper := (rows 97 14 7 25 112 32 64), lower := (rows 97 14 7 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 126 118 120 112 112 112) },{ target := 5, region := (rows 1 10 12 8 16 0 127), good := (rows 65 78 71 95 80 64 64) }] }

theorem profile22_node67 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,17] 6 96 profile22_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,17] 6 96 profile22_node67_cert).mp (by decide +kernel))

def profile22_node68_cert : CutBound 7 := { lost := (rows 0 32 32 0 33 0 0), upper := (rows 97 14 7 41 80 32 64), lower := (rows 97 14 7 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 126 118 120 112 112 112) },{ target := 5, region := (rows 1 10 12 8 127 0 127), good := (rows 81 94 87 95 80 80 80) }] }

theorem profile22_node68 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,33] 6 80 profile22_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,33] 6 80 profile22_node68_cert).mp (by decide +kernel))

def profile22_node69_cert : CutBound 7 := { lost := (rows 0 0 0 1 32 0 0), upper := (rows 97 14 7 56 81 32 64), lower := (rows 97 14 7 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 24 16 127 127), good := (rows 96 110 102 120 120 96 96) },{ target := 5, region := (rows 1 2 4 8 21 0 127), good := (rows 81 94 87 88 80 64 64) }] }

theorem profile22_node69 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,48] 6 65 profile22_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,48] 6 65 profile22_node69_cert).mp (by decide +kernel))

def profile22_node70_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 14 7 104 17 32 64), lower := (rows 97 14 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 104 110 110 104 120 104 104) }] }

theorem profile22_node70 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,96] 6 17 profile22_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3,96] 6 17 profile22_node70_cert).mp (by decide +kernel))

def profile22_node66_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile22_node66_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node66 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,3] 6 (by decide) (choices 2) [17,33,48,96] profile22_node66_route profile22_node66_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node67
  · exact profile22_node68
  · exact profile22_node69
  · exact profile22_node70

def profile22_node72_cert : CutBound 7 := { lost := (rows 0 32 0 32 1 0 0), upper := (rows 97 14 21 11 112 32 64), lower := (rows 97 14 21 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 126 116 122 112 112 112) },{ target := 5, region := (rows 1 6 4 12 16 0 127), good := (rows 65 78 95 75 80 64 64) }] }

theorem profile22_node72 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,3] 6 96 profile22_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,3] 6 96 profile22_node72_cert).mp (by decide +kernel))

def profile22_node73_cert : CutBound 7 := { lost := (rows 0 32 32 0 33 0 0), upper := (rows 97 14 21 41 82 32 64), lower := (rows 97 14 21 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 18 127 127), good := (rows 96 126 116 104 112 96 96) },{ target := 5, region := (rows 1 10 12 8 26 0 127), good := (rows 65 94 85 95 80 64 64) }] }

theorem profile22_node73 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,33] 6 66 profile22_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,33] 6 66 profile22_node73_cert).mp (by decide +kernel))

def profile22_node74_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 14 21 42 81 32 64), lower := (rows 97 14 21 42 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 14 16 127 127), good := (rows 96 110 126 106 112 96 96) }] }

theorem profile22_node74 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,34] 6 65 profile22_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,34] 6 65 profile22_node74_cert).mp (by decide +kernel))

def profile22_node75_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 14 21 104 19 32 64), lower := (rows 97 14 21 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 104 110 126 104 120 104 104) }] }

theorem profile22_node75 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,96] 6 3 profile22_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17,96] 6 3 profile22_node75_cert).mp (by decide +kernel))

def profile22_node71_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node71_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node71 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,17] 6 (by decide) (choices 2) [3,33,34,96] profile22_node71_route profile22_node71_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node72
  · exact profile22_node73
  · exact profile22_node74
  · exact profile22_node75

def profile22_node77_cert : CutBound 7 := { lost := (rows 0 32 32 0 32 0 0), upper := (rows 97 14 22 41 81 32 64), lower := (rows 97 14 22 41 16 32 64), losses := [{ target := 5, region := (rows 1 10 14 8 25 0 127), good := (rows 81 94 86 95 80 64 64) }] }

theorem profile22_node77 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,33] 6 65 profile22_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,33] 6 65 profile22_node77_cert).mp (by decide +kernel))

def profile22_node78_cert : CutBound 7 := { lost := (rows 0 1 1 1 0 0 0), upper := (rows 97 14 22 104 17 32 64), lower := (rows 97 14 22 104 16 32 64), losses := [{ target := 0, region := (rows 0 22 20 127 16 127 127), good := (rows 104 110 126 104 126 104 104) }] }

theorem profile22_node78 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,96] 6 1 profile22_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18,96] 6 1 profile22_node78_cert).mp (by decide +kernel))

def profile22_node76_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile22_node76_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node76 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,18] 6 (by decide) (choices 2) [33,96] profile22_node76_route profile22_node76_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node77
  · exact profile22_node78

def profile22_node79_cert : CutBound 7 := { lost := (rows 0 32 0 32 32 0 0), upper := (rows 97 14 37 91 83 32 64), lower := (rows 97 14 37 8 16 32 64), losses := [{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 65 94 95 72 80 64 64) }] }

theorem profile22_node79 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,33] 6 83 profile22_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,33] 6 83 profile22_node79_cert).mp (by decide +kernel))

def profile22_node80_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 97 14 38 89 81 32 64), lower := (rows 97 14 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 14 8 16 127 127), good := (rows 96 110 102 110 112 96 96) }] }

theorem profile22_node80 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,34] 6 81 profile22_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,34] 6 81 profile22_node80_cert).mp (by decide +kernel))

def profile22_node81_cert : CutBound 7 := { lost := (rows 0 0 65 0 0 0 0), upper := (rows 97 14 52 75 83 32 64), lower := (rows 97 14 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 127 127), good := (rows 96 110 116 104 116 96 96) },{ target := 6, region := (rows 1 2 20 8 16 127 0), good := (rows 33 46 52 40 52 32 32) }] }

theorem profile22_node81 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,48] 6 67 profile22_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,48] 6 67 profile22_node81_cert).mp (by decide +kernel))

def profile22_node82_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 97 14 100 27 19 32 64), lower := (rows 97 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 100 110 100 110 116 100 100) }] }

theorem profile22_node82 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,96] 6 19 profile22_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12,96] 6 19 profile22_node82_cert).mp (by decide +kernel))

def profile22_node65_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile22_node65_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node65 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,12] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile22_node65_route profile22_node65_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node66
  · exact profile22_node71
  · exact profile22_node76
  · exact profile22_node79
  · exact profile22_node80
  · exact profile22_node81
  · exact profile22_node82

def profile22_node83_cert : CutBound 7 := { lost := (rows 0 0 32 32 32 0 0), upper := (rows 97 35 95 95 95 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile22_node83 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,33] 6 95 profile22_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,33] 6 95 profile22_node83_cert).mp (by decide +kernel))

def profile22_node84_cert : CutBound 7 := { lost := (rows 0 65 0 0 0 0 0), upper := (rows 97 38 95 91 91 32 64), lower := (rows 97 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 6, region := (rows 1 6 4 8 16 127 0), good := (rows 33 38 38 40 48 32 32) }] }

theorem profile22_node84 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,36] 6 91 profile22_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,36] 6 91 profile22_node84_cert).mp (by decide +kernel))

def profile22_node86_cert : CutBound 7 := { lost := (rows 0 1 0 32 32 0 0), upper := (rows 97 98 7 29 29 32 64), lower := (rows 97 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 66 95 72 80 64 64) }] }

theorem profile22_node86 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,3] 6 29 profile22_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,3] 6 29 profile22_node86_cert).mp (by decide +kernel))

def profile22_node88_cert : CutBound 7 := { lost := (rows 0 1 0 0 1 0 0), upper := (rows 97 98 13 11 20 32 64), lower := (rows 97 98 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 20 127 127), good := (rows 98 98 126 106 114 98 98) }] }

theorem profile22_node88 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,3] 6 20 profile22_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,3] 6 20 profile22_node88_cert).mp (by decide +kernel))

def profile22_node89_cert : CutBound 7 := { lost := (rows 0 1 0 0 1 0 0), upper := (rows 97 98 13 13 18 32 64), lower := (rows 97 98 13 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 126 126 114 114 114) }] }

theorem profile22_node89 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,5] 6 18 profile22_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,5] 6 18 profile22_node89_cert).mp (by decide +kernel))

def profile22_node90_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 98 13 14 17 32 64), lower := (rows 97 98 13 14 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 12 16 127 127), good := (rows 98 98 110 110 114 98 98) }] }

theorem profile22_node90 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,6] 6 17 profile22_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,6] 6 17 profile22_node90_cert).mp (by decide +kernel))

def profile22_node91_cert : CutBound 7 := { lost := (rows 0 1 0 0 1 0 0), upper := (rows 97 98 13 25 22 32 64), lower := (rows 97 98 13 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 20 127 127), good := (rows 98 98 126 122 114 98 98) }] }

theorem profile22_node91 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,17] 6 6 profile22_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,17] 6 6 profile22_node91_cert).mp (by decide +kernel))

def profile22_node92_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 97 98 13 26 21 32 64), lower := (rows 97 98 13 26 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 24 16 127 127), good := (rows 98 98 110 122 122 98 98) }] }

theorem profile22_node92 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,18] 6 5 profile22_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,18] 6 5 profile22_node92_cert).mp (by decide +kernel))

def profile22_node94_cert : CutBound 7 := { lost := (rows 0 1 32 32 0 0 0), upper := (rows 97 98 13 28 19 32 64), lower := (rows 97 98 13 28 19 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 110 126 114 98 98) },{ target := 5, region := (rows 1 2 20 24 16 0 127), good := (rows 65 66 77 92 95 64 64) }] }

theorem profile22_node94 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,20,3] 6 0 profile22_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,20,3] 6 0 profile22_node94_cert).mp (by decide +kernel))

def profile22_node93_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 40 => 3 | 72 => 3 | 96 => 5 | _ => 0

def profile22_node93_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node93 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9,20] 6 (by decide) (choices 2) [3] profile22_node93_route profile22_node93_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node94

def profile22_node87_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | _ => 0

def profile22_node87_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node87 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,9] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile22_node87_route profile22_node87_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node88
  · exact profile22_node89
  · exact profile22_node90
  · exact profile22_node91
  · exact profile22_node92
  · exact profile22_node93

def profile22_node95_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 97 98 14 29 21 32 64), lower := (rows 97 98 14 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 98 98 110 110 114 98 98) }] }

theorem profile22_node95 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,10] 6 21 profile22_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,10] 6 21 profile22_node95_cert).mp (by decide +kernel))

def profile22_node97_cert : CutBound 7 := { lost := (rows 0 1 32 0 32 0 0), upper := (rows 97 98 28 11 21 32 64), lower := (rows 97 98 28 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 126 106 114 98 98) },{ target := 5, region := (rows 1 2 12 8 24 0 127), good := (rows 65 66 92 95 80 64 64) }] }

theorem profile22_node97 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,3] 6 5 profile22_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,3] 6 5 profile22_node97_cert).mp (by decide +kernel))

def profile22_node99_cert : CutBound 7 := { lost := (rows 0 1 32 32 0 0 0), upper := (rows 97 98 28 13 19 32 64), lower := (rows 97 98 28 13 19 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 126 110 114 98 98) },{ target := 5, region := (rows 1 2 20 24 16 0 127), good := (rows 65 66 92 77 95 64 64) }] }

theorem profile22_node99 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,5,3] 6 0 profile22_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,5,3] 6 0 profile22_node99_cert).mp (by decide +kernel))

def profile22_node98_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 40 => 3 | 72 => 3 | 96 => 5 | _ => 0

def profile22_node98_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node98 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,5] 6 (by decide) (choices 2) [3] profile22_node98_route profile22_node98_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node99

def profile22_node100_cert : CutBound 7 := { lost := (rows 0 1 1 1 0 0 0), upper := (rows 97 98 28 14 17 32 64), lower := (rows 97 98 28 14 16 32 64), losses := [{ target := 0, region := (rows 0 127 20 28 16 127 127), good := (rows 98 98 126 110 126 98 98) }] }

theorem profile22_node100 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,6] 6 1 profile22_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24,6] 6 1 profile22_node100_cert).mp (by decide +kernel))

def profile22_node96_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile22_node96_route : Route 7 := (fun mask => (mask,id))

theorem profile22_node96 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96,24] 6 (by decide) (choices 2) [3,5,6] profile22_node96_route profile22_node96_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node97
  · exact profile22_node98
  · exact profile22_node100

def profile22_node85_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | _ => 0

def profile22_node85_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile22_node85 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96,96] 6 (by decide) (choices 2) [3,9,10,24] profile22_node85_route profile22_node85_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node86
  · exact profile22_node87
  · exact profile22_node95
  · exact profile22_node96

def profile22_node47_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile22_node47_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 48 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 80 => (36,(fun i => match i.val with | 2 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node47 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [96] 6 (by decide) (choices 2) [5,12,33,36,96] profile22_node47_route profile22_node47_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile22_node48
  · exact profile22_node65
  · exact profile22_node83
  · exact profile22_node84
  · exact profile22_node85

def profile22_node0_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile22_node0_route : Route 7 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 18 => (6,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (6,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 24 => (6,(fun i => match i.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 72 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 48 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 80 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile22_node0 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [] 6 (by decide) (choices 2) [6,34,96] profile22_node0_route profile22_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node1
  · exact profile22_node30
  · exact profile22_node47

theorem profile22 : Upper (D (n:=7) [34,33,33,33,33,2,2]) (R (n:=7) [34,33,33,33,33,2,2]) [] 6 := profile22_node0


#print axioms profile22
end Delivery.SmallBudgetTenFinite7
