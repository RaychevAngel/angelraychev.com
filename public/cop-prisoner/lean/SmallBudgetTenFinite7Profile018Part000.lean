import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile18_node3_cert : CutBound 7 := { lost := (rows 32 0 32 2 2 0 0), upper := (rows 7 35 7 105 113 32 64), lower := (rows 7 35 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 15 23 127 127), good := (rows 125 121 125 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node3 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,3] 6 97 profile18_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,3] 6 97 profile18_node3_cert).mp (by decide +kernel))

def profile18_node4_cert : CutBound 7 := { lost := (rows 0 0 2 32 32 0 0), upper := (rows 7 35 37 75 83 32 64), lower := (rows 7 35 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 95 91 93 72 80 64 64) }] }

theorem profile18_node4 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,33] 6 67 profile18_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,33] 6 67 profile18_node4_cert).mp (by decide +kernel))

def profile18_node5_cert : CutBound 7 := { lost := (rows 0 0 1 2 2 0 0), upper := (rows 7 35 38 73 81 32 64), lower := (rows 7 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) }] }

theorem profile18_node5 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,34] 6 65 profile18_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,34] 6 65 profile18_node5_cert).mp (by decide +kernel))

def profile18_node6_cert : CutBound 7 := { lost := (rows 32 0 34 0 0 0 0), upper := (rows 7 35 69 107 115 32 64), lower := (rows 7 35 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 71 69 72 80 64 64) }] }

theorem profile18_node6 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,65] 6 99 profile18_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,65] 6 99 profile18_node6_cert).mp (by decide +kernel))

def profile18_node7_cert : CutBound 7 := { lost := (rows 0 0 1 2 2 0 0), upper := (rows 7 35 70 105 113 32 64), lower := (rows 7 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) }] }

theorem profile18_node7 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,66] 6 97 profile18_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,66] 6 97 profile18_node7_cert).mp (by decide +kernel))

def profile18_node8_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 7 35 100 75 83 32 64), lower := (rows 7 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 95 91 68 72 80 64 64) }] }

theorem profile18_node8 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,96] 6 67 profile18_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33,96] 6 67 profile18_node8_cert).mp (by decide +kernel))

def profile18_node2_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node2 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,33] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile18_node2_route profile18_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node3
  · exact profile18_node4
  · exact profile18_node5
  · exact profile18_node6
  · exact profile18_node7
  · exact profile18_node8

def profile18_node10_cert : CutBound 7 := { lost := (rows 0 1 0 2 2 0 0), upper := (rows 7 98 7 105 113 32 64), lower := (rows 7 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 96 125 104 112 96 96) }] }

theorem profile18_node10 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,3] 6 97 profile18_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,3] 6 97 profile18_node10_cert).mp (by decide +kernel))

def profile18_node11_cert : CutBound 7 := { lost := (rows 0 1 2 32 32 0 0), upper := (rows 7 98 37 75 83 32 64), lower := (rows 7 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 93 72 80 64 64) }] }

theorem profile18_node11 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,33] 6 67 profile18_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,33] 6 67 profile18_node11_cert).mp (by decide +kernel))

def profile18_node12_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 7 98 38 73 81 32 64), lower := (rows 7 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 100 104 112 96 96) }] }

theorem profile18_node12 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,34] 6 65 profile18_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,34] 6 65 profile18_node12_cert).mp (by decide +kernel))

def profile18_node13_cert : CutBound 7 := { lost := (rows 0 1 3 0 0 0 0), upper := (rows 7 98 100 11 19 32 64), lower := (rows 7 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 100 100 108 116 100 100) }] }

theorem profile18_node13 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,96] 6 3 profile18_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96,96] 6 3 profile18_node13_cert).mp (by decide +kernel))

def profile18_node9_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node9_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile18_node9 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6,96] 6 (by decide) (choices 2) [3,33,34,96] profile18_node9_route profile18_node9_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node10
  · exact profile18_node11
  · exact profile18_node12
  · exact profile18_node13

def profile18_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile18_node1 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [6] 6 (by decide) (choices 2) [33,96] profile18_node1_route profile18_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile18_node2
  · exact profile18_node9

def profile18_node16_cert : CutBound 7 := { lost := (rows 0 32 32 2 2 0 0), upper := (rows 35 7 7 105 113 32 64), lower := (rows 35 7 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 15 23 127 127), good := (rows 121 125 125 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node16 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,3] 6 97 profile18_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,3] 6 97 profile18_node16_cert).mp (by decide +kernel))

def profile18_node17_cert : CutBound 7 := { lost := (rows 0 32 2 32 32 0 0), upper := (rows 35 7 37 75 83 32 64), lower := (rows 35 7 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 6 4 15 23 0 127), good := (rows 91 95 95 72 80 64 64) }] }

theorem profile18_node17 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,33] 6 67 profile18_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,33] 6 67 profile18_node17_cert).mp (by decide +kernel))

def profile18_node18_cert : CutBound 7 := { lost := (rows 0 0 1 2 2 0 0), upper := (rows 35 7 38 73 81 32 64), lower := (rows 35 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) }] }

theorem profile18_node18 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,34] 6 65 profile18_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,34] 6 65 profile18_node18_cert).mp (by decide +kernel))

def profile18_node19_cert : CutBound 7 := { lost := (rows 0 32 34 0 0 0 0), upper := (rows 35 7 69 107 115 32 64), lower := (rows 35 7 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node19 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,65] 6 99 profile18_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,65] 6 99 profile18_node19_cert).mp (by decide +kernel))

def profile18_node20_cert : CutBound 7 := { lost := (rows 0 0 1 2 2 0 0), upper := (rows 35 7 70 105 113 32 64), lower := (rows 35 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) }] }

theorem profile18_node20 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,66] 6 97 profile18_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,66] 6 97 profile18_node20_cert).mp (by decide +kernel))

def profile18_node21_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 35 7 100 75 83 32 64), lower := (rows 35 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 91 95 68 72 80 64 64) }] }

theorem profile18_node21 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,96] 6 67 profile18_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5,96] 6 67 profile18_node21_cert).mp (by decide +kernel))

def profile18_node15_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node15 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,5] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile18_node15_route profile18_node15_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node16
  · exact profile18_node17
  · exact profile18_node18
  · exact profile18_node19
  · exact profile18_node20
  · exact profile18_node21

def profile18_node22_cert : CutBound 7 := { lost := (rows 0 0 32 32 32 0 0), upper := (rows 35 35 71 79 87 32 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile18_node22 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,33] 6 71 profile18_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,33] 6 71 profile18_node22_cert).mp (by decide +kernel))

def profile18_node23_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 38 71 75 83 32 64), lower := (rows 35 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) }] }

theorem profile18_node23 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,36] 6 67 profile18_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,36] 6 67 profile18_node23_cert).mp (by decide +kernel))

def profile18_node25_cert : CutBound 7 := { lost := (rows 0 32 32 2 2 0 0), upper := (rows 35 67 7 109 117 32 64), lower := (rows 35 67 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 97 125 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node25 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,3] 6 101 profile18_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,3] 6 101 profile18_node25_cert).mp (by decide +kernel))

def profile18_node26_cert : CutBound 7 := { lost := (rows 0 32 2 32 32 0 0), upper := (rows 35 67 37 79 87 32 64), lower := (rows 35 67 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 4 12 20 0 127), good := (rows 67 67 95 72 80 64 64) }] }

theorem profile18_node26 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,33] 6 71 profile18_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,33] 6 71 profile18_node26_cert).mp (by decide +kernel))

def profile18_node27_cert : CutBound 7 := { lost := (rows 64 32 65 0 0 0 0), upper := (rows 35 67 38 77 85 32 64), lower := (rows 35 67 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 70 72 80 64 64) },{ target := 6, region := (rows 7 2 7 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile18_node27 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,34] 6 69 profile18_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,34] 6 69 profile18_node27_cert).mp (by decide +kernel))

def profile18_node28_cert : CutBound 7 := { lost := (rows 0 32 34 0 0 0 0), upper := (rows 35 67 69 47 55 32 64), lower := (rows 35 67 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node28 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,65] 6 39 profile18_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,65] 6 39 profile18_node28_cert).mp (by decide +kernel))

def profile18_node29_cert : CutBound 7 := { lost := (rows 0 32 33 0 0 0 0), upper := (rows 35 67 70 45 53 32 64), lower := (rows 35 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) }] }

theorem profile18_node29 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,66] 6 37 profile18_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,66] 6 37 profile18_node29_cert).mp (by decide +kernel))

def profile18_node30_cert : CutBound 7 := { lost := (rows 0 32 3 0 0 0 0), upper := (rows 35 67 100 15 23 32 64), lower := (rows 35 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) }] }

theorem profile18_node30 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,96] 6 7 profile18_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65,96] 6 7 profile18_node30_cert).mp (by decide +kernel))

def profile18_node24_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node24_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node24 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,65] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile18_node24_route profile18_node24_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node25
  · exact profile18_node26
  · exact profile18_node27
  · exact profile18_node28
  · exact profile18_node29
  · exact profile18_node30

def profile18_node31_cert : CutBound 7 := { lost := (rows 64 33 0 0 0 0 0), upper := (rows 35 70 103 107 115 32 64), lower := (rows 35 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 70 70 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 39 36 40 48 32 32) }] }

theorem profile18_node31 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,68] 6 99 profile18_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,68] 6 99 profile18_node31_cert).mp (by decide +kernel))

def profile18_node32_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 98 71 79 87 32 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile18_node32 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,96] 6 71 profile18_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34,96] 6 71 profile18_node32_cert).mp (by decide +kernel))

def profile18_node14_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node14_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node14 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [34] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile18_node14_route profile18_node14_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node15
  · exact profile18_node22
  · exact profile18_node23
  · exact profile18_node24
  · exact profile18_node31
  · exact profile18_node32

def profile18_node34_cert : CutBound 7 := { lost := (rows 2 0 32 32 32 0 0), upper := (rows 37 35 71 75 83 32 64), lower := (rows 37 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 69 95 68 72 80 64 64) }] }

theorem profile18_node34 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,33] 6 67 profile18_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,33] 6 67 profile18_node34_cert).mp (by decide +kernel))

def profile18_node35_cert : CutBound 7 := { lost := (rows 66 32 0 0 0 0 0), upper := (rows 37 67 103 107 115 32 64), lower := (rows 37 67 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 71 67 68 72 80 64 64) },{ target := 6, region := (rows 5 2 4 8 16 127 0), good := (rows 37 35 37 40 48 32 32) }] }

theorem profile18_node35 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,65] 6 99 profile18_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,65] 6 99 profile18_node35_cert).mp (by decide +kernel))

def profile18_node36_cert : CutBound 7 := { lost := (rows 66 1 0 0 0 0 0), upper := (rows 37 98 71 75 83 32 64), lower := (rows 37 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 6, region := (rows 5 2 4 8 16 127 0), good := (rows 37 34 37 40 48 32 32) }] }

theorem profile18_node36 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,96] 6 67 profile18_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36,96] 6 67 profile18_node36_cert).mp (by decide +kernel))

def profile18_node33_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node33 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [36] 6 (by decide) (choices 2) [33,65,96] profile18_node33_route profile18_node33_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile18_node34
  · exact profile18_node35
  · exact profile18_node36

def profile18_node39_cert : CutBound 7 := { lost := (rows 2 32 32 0 0 0 0), upper := (rows 97 7 7 107 115 32 64), lower := (rows 97 7 7 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile18_node39 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,3] 6 99 profile18_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,3] 6 99 profile18_node39_cert).mp (by decide +kernel))

def profile18_node40_cert : CutBound 7 := { lost := (rows 2 32 2 32 32 0 0), upper := (rows 97 7 37 75 83 32 64), lower := (rows 97 7 37 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 5, region := (rows 1 6 4 14 22 0 127), good := (rows 65 95 95 72 80 64 64) }] }

theorem profile18_node40 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,33] 6 67 profile18_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,33] 6 67 profile18_node40_cert).mp (by decide +kernel))

def profile18_node41_cert : CutBound 7 := { lost := (rows 2 0 1 32 32 0 0), upper := (rows 97 7 38 75 83 32 64), lower := (rows 97 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 94 72 80 64 64) }] }

theorem profile18_node41 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,34] 6 67 profile18_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,34] 6 67 profile18_node41_cert).mp (by decide +kernel))

def profile18_node42_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 97 7 100 11 19 32 64), lower := (rows 97 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) }] }

theorem profile18_node42 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,96] 6 3 profile18_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5,96] 6 3 profile18_node42_cert).mp (by decide +kernel))

def profile18_node38_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node38_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile18_node38 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,5] 6 (by decide) (choices 2) [3,33,34,96] profile18_node38_route profile18_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node39
  · exact profile18_node40
  · exact profile18_node41
  · exact profile18_node42

def profile18_node43_cert : CutBound 7 := { lost := (rows 2 0 32 32 32 0 0), upper := (rows 97 35 71 79 87 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile18_node43 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,33] 6 71 profile18_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,33] 6 71 profile18_node43_cert).mp (by decide +kernel))

def profile18_node44_cert : CutBound 7 := { lost := (rows 2 65 0 0 0 0 0), upper := (rows 97 38 71 75 83 32 64), lower := (rows 97 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 6, region := (rows 1 6 4 8 16 127 0), good := (rows 33 38 38 40 48 32 32) }] }

theorem profile18_node44 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,36] 6 67 profile18_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,36] 6 67 profile18_node44_cert).mp (by decide +kernel))

def profile18_node46_cert : CutBound 7 := { lost := (rows 2 1 0 32 32 0 0), upper := (rows 97 98 7 15 23 32 64), lower := (rows 97 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 66 95 72 80 64 64) }] }

theorem profile18_node46 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,96,3] 6 7 profile18_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,96,3] 6 7 profile18_node46_cert).mp (by decide +kernel))

def profile18_node45_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile18_node45_route : Route 7 := (fun mask => (mask,id))

theorem profile18_node45 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96,96] 6 (by decide) (choices 2) [3] profile18_node45_route profile18_node45_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node46

def profile18_node37_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node37_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile18_node37 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [96] 6 (by decide) (choices 2) [5,33,36,96] profile18_node37_route profile18_node37_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node38
  · exact profile18_node43
  · exact profile18_node44
  · exact profile18_node45

def profile18_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 18 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile18_node0_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile18_node0 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [] 6 (by decide) (choices 2) [6,34,36,96] profile18_node0_route profile18_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node1
  · exact profile18_node14
  · exact profile18_node33
  · exact profile18_node37

theorem profile18 : Upper (D (n:=7) [35,34,33,32,32,2,2]) (R (n:=7) [35,34,33,32,32,2,2]) [] 6 := profile18_node0


#print axioms profile18
end Delivery.SmallBudgetTenFinite7
