import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile19_node2_cert : CutBound 7 := { lost := (rows 96 96 0 4 4 0 0), upper := (rows 7 7 103 107 115 32 64), lower := (rows 7 7 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 11 19 127 127), good := (rows 123 123 96 104 112 96 96) },{ target := 5, region := (rows 7 7 4 8 16 0 127), good := (rows 71 71 71 72 80 64 64) },{ target := 6, region := (rows 7 7 4 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile19_node2 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,5] 6 99 profile19_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,5] 6 99 profile19_node2_cert).mp (by decide +kernel))

def profile19_node4_cert : CutBound 7 := { lost := (rows 32 4 32 3 3 0 0), upper := (rows 7 35 7 108 116 32 64), lower := (rows 7 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 13 21 127 127), good := (rows 126 122 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 121 125 104 112 96 96) },{ target := 2, region := (rows 1 7 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node4 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,3] 6 100 profile19_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,3] 6 100 profile19_node4_cert).mp (by decide +kernel))

def profile19_node5_cert : CutBound 7 := { lost := (rows 0 4 2 33 33 0 0), upper := (rows 7 35 37 78 86 32 64), lower := (rows 7 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 9 17 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 1 7 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 91 93 72 80 64 64) }] }

theorem profile19_node5 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,33] 6 70 profile19_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,33] 6 70 profile19_node5_cert).mp (by decide +kernel))

def profile19_node6_cert : CutBound 7 := { lost := (rows 32 4 1 34 34 0 0), upper := (rows 7 35 38 77 85 32 64), lower := (rows 7 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 121 100 104 112 96 96) },{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 99 99 98 104 112 96 96) },{ target := 5, region := (rows 5 2 4 13 21 0 127), good := (rows 95 91 95 72 80 64 64) }] }

theorem profile19_node6 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,34] 6 69 profile19_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,34] 6 69 profile19_node6_cert).mp (by decide +kernel))

def profile19_node7_cert : CutBound 7 := { lost := (rows 32 4 34 1 1 0 0), upper := (rows 7 35 69 110 118 32 64), lower := (rows 7 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 9 17 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 1 7 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 71 69 72 80 64 64) }] }

theorem profile19_node7 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,65] 6 102 profile19_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,65] 6 102 profile19_node7_cert).mp (by decide +kernel))

def profile19_node8_cert : CutBound 7 := { lost := (rows 32 4 33 2 2 0 0), upper := (rows 7 35 70 109 117 32 64), lower := (rows 7 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 121 100 104 112 96 96) },{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 99 99 98 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node8 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,66] 6 101 profile19_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,66] 6 101 profile19_node8_cert).mp (by decide +kernel))

def profile19_node9_cert : CutBound 7 := { lost := (rows 64 68 3 32 32 0 0), upper := (rows 7 35 100 79 87 32 64), lower := (rows 7 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 2, region := (rows 1 3 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 91 68 72 80 64 64) },{ target := 6, region := (rows 5 7 4 8 16 127 0), good := (rows 39 35 39 40 48 32 32) }] }

theorem profile19_node9 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,96] 6 71 profile19_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33,96] 6 71 profile19_node9_cert).mp (by decide +kernel))

def profile19_node3_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node3 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,33] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile19_node3_route profile19_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node4
  · exact profile19_node5
  · exact profile19_node6
  · exact profile19_node7
  · exact profile19_node8
  · exact profile19_node9

def profile19_node10_cert : CutBound 7 := { lost := (rows 96 65 0 4 4 0 0), upper := (rows 7 38 103 107 115 32 64), lower := (rows 7 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 7 4 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 2, region := (rows 1 2 0 9 17 127 127), good := (rows 123 98 96 104 112 96 96) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 71 71 68 72 80 64 64) },{ target := 6, region := (rows 7 7 4 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile19_node10 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,36] 6 99 profile19_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,36] 6 99 profile19_node10_cert).mp (by decide +kernel))

def profile19_node12_cert : CutBound 7 := { lost := (rows 32 5 32 2 2 0 0), upper := (rows 7 98 7 109 117 32 64), lower := (rows 7 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 96 125 104 112 96 96) },{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 99 98 99 106 114 98 98) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node12 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,3] 6 101 profile19_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,3] 6 101 profile19_node12_cert).mp (by decide +kernel))

def profile19_node13_cert : CutBound 7 := { lost := (rows 64 5 66 32 32 0 0), upper := (rows 7 98 37 79 87 32 64), lower := (rows 7 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 99 98 99 106 114 98 98) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 93 72 80 64 64) },{ target := 6, region := (rows 3 2 7 8 16 127 0), good := (rows 39 39 37 40 48 32 32) }] }

theorem profile19_node13 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,33] 6 71 profile19_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,33] 6 71 profile19_node13_cert).mp (by decide +kernel))

def profile19_node14_cert : CutBound 7 := { lost := (rows 32 5 1 34 34 0 0), upper := (rows 7 98 38 77 85 32 64), lower := (rows 7 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 100 104 112 96 96) },{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 99 98 98 106 114 98 98) },{ target := 5, region := (rows 5 2 4 13 21 0 127), good := (rows 95 66 95 72 80 64 64) }] }

theorem profile19_node14 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,34] 6 69 profile19_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,34] 6 69 profile19_node14_cert).mp (by decide +kernel))

def profile19_node15_cert : CutBound 7 := { lost := (rows 0 5 3 32 32 0 0), upper := (rows 7 98 100 15 23 32 64), lower := (rows 7 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 100 100 108 116 100 100) },{ target := 2, region := (rows 1 127 0 8 16 127 127), good := (rows 99 98 98 106 114 98 98) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile19_node15 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,96] 6 7 profile19_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96,96] 6 7 profile19_node15_cert).mp (by decide +kernel))

def profile19_node11_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node11_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile19_node11 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6,96] 6 (by decide) (choices 2) [3,33,34,96] profile19_node11_route profile19_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node12
  · exact profile19_node13
  · exact profile19_node14
  · exact profile19_node15

def profile19_node1_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile19_node1 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [6] 6 (by decide) (choices 2) [5,33,36,96] profile19_node1_route profile19_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node2
  · exact profile19_node3
  · exact profile19_node10
  · exact profile19_node11

def profile19_node18_cert : CutBound 7 := { lost := (rows 4 32 32 3 3 0 0), upper := (rows 35 7 7 108 116 32 64), lower := (rows 35 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 122 126 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 14 22 127 127), good := (rows 121 125 125 104 112 96 96) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node18 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,3] 6 100 profile19_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,3] 6 100 profile19_node18_cert).mp (by decide +kernel))

def profile19_node19_cert : CutBound 7 := { lost := (rows 4 32 2 33 33 0 0), upper := (rows 35 7 37 78 86 32 64), lower := (rows 35 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 122 126 100 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 97 104 112 96 96) },{ target := 5, region := (rows 1 6 4 14 22 0 127), good := (rows 91 95 95 72 80 64 64) }] }

theorem profile19_node19 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,33] 6 70 profile19_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,33] 6 70 profile19_node19_cert).mp (by decide +kernel))

def profile19_node20_cert : CutBound 7 := { lost := (rows 4 0 1 34 34 0 0), upper := (rows 35 7 38 77 85 32 64), lower := (rows 35 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 10 18 127 127), good := (rows 121 125 124 104 112 96 96) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 91 95 94 72 80 64 64) }] }

theorem profile19_node20 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,34] 6 69 profile19_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,34] 6 69 profile19_node20_cert).mp (by decide +kernel))

def profile19_node21_cert : CutBound 7 := { lost := (rows 4 32 34 1 1 0 0), upper := (rows 35 7 69 110 118 32 64), lower := (rows 35 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 122 126 100 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 97 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node21 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,65] 6 102 profile19_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,65] 6 102 profile19_node21_cert).mp (by decide +kernel))

def profile19_node22_cert : CutBound 7 := { lost := (rows 4 32 33 2 2 0 0), upper := (rows 35 7 70 109 117 32 64), lower := (rows 35 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 10 18 127 127), good := (rows 121 125 124 104 112 96 96) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) }] }

theorem profile19_node22 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,66] 6 101 profile19_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,66] 6 101 profile19_node22_cert).mp (by decide +kernel))

def profile19_node23_cert : CutBound 7 := { lost := (rows 68 64 3 32 32 0 0), upper := (rows 35 7 100 79 87 32 64), lower := (rows 35 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 91 95 68 72 80 64 64) },{ target := 6, region := (rows 7 6 4 8 16 127 0), good := (rows 35 39 39 40 48 32 32) }] }

theorem profile19_node23 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,96] 6 71 profile19_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5,96] 6 71 profile19_node23_cert).mp (by decide +kernel))

def profile19_node17_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node17_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node17 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,5] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile19_node17_route profile19_node17_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node18
  · exact profile19_node19
  · exact profile19_node20
  · exact profile19_node21
  · exact profile19_node22
  · exact profile19_node23

def profile19_node24_cert : CutBound 7 := { lost := (rows 68 68 32 32 32 0 0), upper := (rows 35 35 71 79 87 32 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) },{ target := 6, region := (rows 127 127 4 8 16 127 0), good := (rows 35 35 39 43 51 35 35) }] }

theorem profile19_node24 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,33] 6 71 profile19_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,33] 6 71 profile19_node24_cert).mp (by decide +kernel))

def profile19_node25_cert : CutBound 7 := { lost := (rows 68 65 32 32 32 0 0), upper := (rows 35 38 71 79 87 32 64), lower := (rows 35 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) },{ target := 6, region := (rows 7 6 4 8 16 127 0), good := (rows 35 39 39 40 48 32 32) }] }

theorem profile19_node25 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,36] 6 71 profile19_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,36] 6 71 profile19_node25_cert).mp (by decide +kernel))

def profile19_node27_cert : CutBound 7 := { lost := (rows 4 4 0 3 3 0 0), upper := (rows 35 67 7 108 116 32 64), lower := (rows 35 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 127 127), good := (rows 98 98 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 97 125 104 112 96 96) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) }] }

theorem profile19_node27 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,3] 6 100 profile19_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,3] 6 100 profile19_node27_cert).mp (by decide +kernel))

def profile19_node28_cert : CutBound 7 := { lost := (rows 4 36 2 32 32 0 0), upper := (rows 35 67 37 78 86 32 64), lower := (rows 35 67 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 7 4 12 20 0 127), good := (rows 67 67 95 72 80 64 64) }] }

theorem profile19_node28 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,33] 6 70 profile19_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,33] 6 70 profile19_node28_cert).mp (by decide +kernel))

def profile19_node29_cert : CutBound 7 := { lost := (rows 68 36 65 0 0 0 0), upper := (rows 35 67 38 77 85 32 64), lower := (rows 35 67 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 70 72 80 64 64) },{ target := 6, region := (rows 7 2 7 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile19_node29 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,34] 6 69 profile19_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,34] 6 69 profile19_node29_cert).mp (by decide +kernel))

def profile19_node30_cert : CutBound 7 := { lost := (rows 68 36 34 0 0 0 0), upper := (rows 35 67 69 46 54 32 64), lower := (rows 35 67 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 37 40 48 32 32) }] }

theorem profile19_node30 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,65] 6 38 profile19_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,65] 6 38 profile19_node30_cert).mp (by decide +kernel))

def profile19_node31_cert : CutBound 7 := { lost := (rows 68 36 33 64 64 0 0), upper := (rows 35 67 70 45 53 32 64), lower := (rows 35 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) },{ target := 6, region := (rows 7 2 4 12 20 127 0), good := (rows 35 35 63 40 48 32 32) }] }

theorem profile19_node31 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,66] 6 37 profile19_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,66] 6 37 profile19_node31_cert).mp (by decide +kernel))

def profile19_node32_cert : CutBound 7 := { lost := (rows 68 36 3 0 0 0 0), upper := (rows 35 67 100 15 23 32 64), lower := (rows 35 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 36 40 48 32 32) }] }

theorem profile19_node32 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,96] 6 7 profile19_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65,96] 6 7 profile19_node32_cert).mp (by decide +kernel))

def profile19_node26_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node26 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,65] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile19_node26_route profile19_node26_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node27
  · exact profile19_node28
  · exact profile19_node29
  · exact profile19_node30
  · exact profile19_node31
  · exact profile19_node32

def profile19_node34_cert : CutBound 7 := { lost := (rows 4 33 32 2 2 0 0), upper := (rows 35 70 7 109 117 32 64), lower := (rows 35 70 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 124 125 104 112 96 96) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 7 5 8 16 0 127), good := (rows 71 70 71 72 80 64 64) }] }

theorem profile19_node34 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,3] 6 101 profile19_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,3] 6 101 profile19_node34_cert).mp (by decide +kernel))

def profile19_node35_cert : CutBound 7 := { lost := (rows 4 33 2 32 32 0 0), upper := (rows 35 70 37 79 87 32 64), lower := (rows 35 70 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 100 101 104 112 96 96) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 97 104 112 96 96) },{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 67 94 95 72 80 64 64) }] }

theorem profile19_node35 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,33] 6 71 profile19_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,33] 6 71 profile19_node35_cert).mp (by decide +kernel))

def profile19_node36_cert : CutBound 7 := { lost := (rows 68 33 65 0 0 0 0), upper := (rows 35 70 38 77 85 32 64), lower := (rows 35 70 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 70 70 72 80 64 64) },{ target := 6, region := (rows 7 2 7 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile19_node36 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,34] 6 69 profile19_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,34] 6 69 profile19_node36_cert).mp (by decide +kernel))

def profile19_node37_cert : CutBound 7 := { lost := (rows 68 33 34 64 64 0 0), upper := (rows 35 70 69 47 55 32 64), lower := (rows 35 70 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 100 101 104 112 96 96) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 97 104 112 96 96) },{ target := 5, region := (rows 1 7 5 8 16 0 127), good := (rows 71 70 71 72 80 64 64) },{ target := 6, region := (rows 3 2 4 10 18 127 0), good := (rows 59 63 37 40 48 32 32) }] }

theorem profile19_node37 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,65] 6 39 profile19_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,65] 6 39 profile19_node37_cert).mp (by decide +kernel))

def profile19_node38_cert : CutBound 7 := { lost := (rows 68 33 33 64 64 0 0), upper := (rows 35 70 70 45 53 32 64), lower := (rows 35 70 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 2, region := (rows 7 2 0 8 16 127 127), good := (rows 99 99 99 104 112 96 96) },{ target := 5, region := (rows 1 127 127 8 16 0 127), good := (rows 71 70 70 78 86 70 70) },{ target := 6, region := (rows 7 2 4 14 22 127 0), good := (rows 59 63 63 40 48 32 32) }] }

theorem profile19_node38 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,66] 6 37 profile19_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,66] 6 37 profile19_node38_cert).mp (by decide +kernel))

def profile19_node39_cert : CutBound 7 := { lost := (rows 68 33 3 64 64 0 0), upper := (rows 35 70 100 15 23 32 64), lower := (rows 35 70 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 100 100 108 116 100 100) },{ target := 2, region := (rows 3 2 0 8 16 127 127), good := (rows 99 99 96 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 70 70 72 80 64 64) },{ target := 6, region := (rows 3 2 4 10 18 127 0), good := (rows 59 63 36 40 48 32 32) }] }

theorem profile19_node39 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,96] 6 7 profile19_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68,96] 6 7 profile19_node39_cert).mp (by decide +kernel))

def profile19_node33_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node33_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node33 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,68] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile19_node33_route profile19_node33_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node34
  · exact profile19_node35
  · exact profile19_node36
  · exact profile19_node37
  · exact profile19_node38
  · exact profile19_node39

def profile19_node40_cert : CutBound 7 := { lost := (rows 4 5 32 32 32 0 0), upper := (rows 35 98 71 79 87 32 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile19_node40 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,96] 6 71 profile19_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34,96] 6 71 profile19_node40_cert).mp (by decide +kernel))

def profile19_node16_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node16_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node16 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [34] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile19_node16_route profile19_node16_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile19_node17
  · exact profile19_node24
  · exact profile19_node25
  · exact profile19_node26
  · exact profile19_node33
  · exact profile19_node40

def profile19_node43_cert : CutBound 7 := { lost := (rows 6 32 32 1 1 0 0), upper := (rows 97 7 7 110 118 32 64), lower := (rows 97 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 96 126 126 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 99 105 113 97 97) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile19_node43 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,3] 6 102 profile19_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,3] 6 102 profile19_node43_cert).mp (by decide +kernel))

def profile19_node44_cert : CutBound 7 := { lost := (rows 6 32 2 33 33 0 0), upper := (rows 97 7 37 78 86 32 64), lower := (rows 97 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 96 126 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 97 105 113 97 97) },{ target := 5, region := (rows 1 6 4 14 22 0 127), good := (rows 65 95 95 72 80 64 64) }] }

theorem profile19_node44 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,33] 6 70 profile19_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,33] 6 70 profile19_node44_cert).mp (by decide +kernel))

def profile19_node45_cert : CutBound 7 := { lost := (rows 6 64 65 32 32 0 0), upper := (rows 97 7 38 79 87 32 64), lower := (rows 97 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 99 105 113 97 97) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 94 72 80 64 64) },{ target := 6, region := (rows 1 3 7 8 16 127 0), good := (rows 39 39 38 40 48 32 32) }] }

theorem profile19_node45 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,34] 6 71 profile19_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,34] 6 71 profile19_node45_cert).mp (by decide +kernel))

def profile19_node46_cert : CutBound 7 := { lost := (rows 6 0 3 32 32 0 0), upper := (rows 97 7 100 15 23 32 64), lower := (rows 97 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 97 105 113 97 97) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile19_node46 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,96] 6 7 profile19_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5,96] 6 7 profile19_node46_cert).mp (by decide +kernel))

def profile19_node42_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node42_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile19_node42 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,5] 6 (by decide) (choices 2) [3,33,34,96] profile19_node42_route profile19_node42_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node43
  · exact profile19_node44
  · exact profile19_node45
  · exact profile19_node46

def profile19_node47_cert : CutBound 7 := { lost := (rows 6 4 32 32 32 0 0), upper := (rows 97 35 71 79 87 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile19_node47 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,33] 6 71 profile19_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,33] 6 71 profile19_node47_cert).mp (by decide +kernel))

def profile19_node49_cert : CutBound 7 := { lost := (rows 6 65 64 32 32 0 0), upper := (rows 97 38 7 79 87 32 64), lower := (rows 97 38 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 99 105 113 97 97) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 94 95 72 80 64 64) },{ target := 6, region := (rows 1 7 5 8 16 127 0), good := (rows 39 38 39 40 48 32 32) }] }

theorem profile19_node49 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,3] 6 71 profile19_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,3] 6 71 profile19_node49_cert).mp (by decide +kernel))

def profile19_node50_cert : CutBound 7 := { lost := (rows 6 65 34 64 64 0 0), upper := (rows 97 38 69 15 23 32 64), lower := (rows 97 38 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 97 105 113 97 97) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 69 70 69 72 80 64 64) },{ target := 6, region := (rows 1 6 4 12 20 127 0), good := (rows 33 62 63 40 48 32 32) }] }

theorem profile19_node50 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,65] 6 7 profile19_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,65] 6 7 profile19_node50_cert).mp (by decide +kernel))

def profile19_node51_cert : CutBound 7 := { lost := (rows 6 65 33 0 0 0 0), upper := (rows 97 38 70 15 23 32 64), lower := (rows 97 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 2, region := (rows 127 2 0 8 16 127 127), good := (rows 97 99 99 105 113 97 97) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 65 70 70 72 80 64 64) },{ target := 6, region := (rows 1 6 4 8 16 127 0), good := (rows 33 38 38 40 48 32 32) }] }

theorem profile19_node51 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,66] 6 7 profile19_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36,66] 6 7 profile19_node51_cert).mp (by decide +kernel))

def profile19_node48_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile19_node48_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node48 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,36] 6 (by decide) (choices 2) [3,65,66] profile19_node48_route profile19_node48_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node49
  · exact profile19_node50
  · exact profile19_node51

def profile19_node53_cert : CutBound 7 := { lost := (rows 6 5 0 32 32 0 0), upper := (rows 97 98 7 15 23 32 64), lower := (rows 97 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 2, region := (rows 127 127 0 8 16 127 127), good := (rows 99 99 99 107 115 99 99) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 66 95 72 80 64 64) }] }

theorem profile19_node53 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,96,3] 6 7 profile19_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,96,3] 6 7 profile19_node53_cert).mp (by decide +kernel))

def profile19_node52_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile19_node52_route : Route 7 := (fun mask => (mask,id))

theorem profile19_node52 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96,96] 6 (by decide) (choices 2) [3] profile19_node52_route profile19_node52_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node53

def profile19_node41_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node41_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile19_node41 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [96] 6 (by decide) (choices 2) [5,33,36,96] profile19_node41_route profile19_node41_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile19_node42
  · exact profile19_node47
  · exact profile19_node48
  · exact profile19_node52

def profile19_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 18 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile19_node0_route : Route 7 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile19_node0 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [] 6 (by decide) (choices 2) [6,34,96] profile19_node0_route profile19_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node1
  · exact profile19_node16
  · exact profile19_node41

theorem profile19 : Upper (D (n:=7) [34,34,34,32,32,2,2]) (R (n:=7) [34,34,34,32,32,2,2]) [] 6 := profile19_node0


#print axioms profile19
end Delivery.SmallBudgetTenFinite7
