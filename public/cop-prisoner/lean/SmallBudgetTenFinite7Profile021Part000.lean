import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile21_node3_cert : CutBound 7 := { lost := (rows 0 0 0 3 3 0 0), upper := (rows 7 11 7 104 112 32 64), lower := (rows 7 11 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 125 120 120 120 120) }] }

theorem profile21_node3 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,3] 6 96 profile21_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,3] 6 96 profile21_node3_cert).mp (by decide +kernel))

def profile21_node4_cert : CutBound 7 := { lost := (rows 64 64 66 1 1 0 0), upper := (rows 7 11 37 106 114 32 64), lower := (rows 7 11 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 109 101 104 112 96 96) },{ target := 6, region := (rows 11 10 15 8 16 127 0), good := (rows 39 47 37 47 48 32 32) }] }

theorem profile21_node4 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,33] 6 98 profile21_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,33] 6 98 profile21_node4_cert).mp (by decide +kernel))

def profile21_node5_cert : CutBound 7 := { lost := (rows 32 0 1 2 2 0 0), upper := (rows 7 11 38 105 113 32 64), lower := (rows 7 11 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 110 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) },{ target := 5, region := (rows 5 2 4 8 16 0 127), good := (rows 71 75 71 72 80 64 64) }] }

theorem profile21_node5 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,34] 6 97 profile21_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,34] 6 97 profile21_node5_cert).mp (by decide +kernel))

def profile21_node7_cert : CutBound 7 := { lost := (rows 0 0 3 0 3 0 0), upper := (rows 7 11 100 11 112 32 64), lower := (rows 7 11 100 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 126 116 126 116 116 116) },{ target := 1, region := (rows 1 0 127 8 127 127 127), good := (rows 117 125 116 125 116 116 116) }] }

theorem profile21_node7 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,3] 6 96 profile21_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,3] 6 96 profile21_node7_cert).mp (by decide +kernel))

def profile21_node8_cert : CutBound 7 := { lost := (rows 0 0 3 2 1 0 0), upper := (rows 7 11 100 41 82 32 64), lower := (rows 7 11 100 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 19 127 127), good := (rows 118 126 100 124 116 100 100) },{ target := 1, region := (rows 1 0 127 11 16 127 127), good := (rows 109 109 100 109 116 100 100) }] }

theorem profile21_node8 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,33] 6 66 profile21_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,33] 6 66 profile21_node8_cert).mp (by decide +kernel))

def profile21_node9_cert : CutBound 7 := { lost := (rows 0 0 3 1 2 0 0), upper := (rows 7 11 100 42 81 32 64), lower := (rows 7 11 100 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 11 16 127 127), good := (rows 110 110 100 110 116 100 100) },{ target := 1, region := (rows 1 0 127 8 19 127 127), good := (rows 117 125 100 124 116 100 100) }] }

theorem profile21_node9 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,34] 6 65 profile21_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,34] 6 65 profile21_node9_cert).mp (by decide +kernel))

def profile21_node10_cert : CutBound 7 := { lost := (rows 0 0 3 3 0 0 0), upper := (rows 7 11 100 104 19 32 64), lower := (rows 7 11 100 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 127 16 127 127), good := (rows 110 110 108 108 124 108 108) },{ target := 1, region := (rows 1 0 127 127 16 127 127), good := (rows 109 109 108 108 124 108 108) }] }

theorem profile21_node10 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,96] 6 3 profile21_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96,96] 6 3 profile21_node10_cert).mp (by decide +kernel))

def profile21_node6_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node6_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node6 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9,96] 6 (by decide) (choices 2) [3,33,34,96] profile21_node6_route profile21_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node7
  · exact profile21_node8
  · exact profile21_node9
  · exact profile21_node10

def profile21_node2_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node2_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node2 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,9] 6 (by decide) (choices 2) [3,33,34,96] profile21_node2_route profile21_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node3
  · exact profile21_node4
  · exact profile21_node5
  · exact profile21_node6

def profile21_node12_cert : CutBound 7 := { lost := (rows 0 0 0 3 3 0 0), upper := (rows 7 35 7 104 120 32 64), lower := (rows 7 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 125 121 125 120 120 120 120) }] }

theorem profile21_node12 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,3] 6 104 profile21_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,3] 6 104 profile21_node12_cert).mp (by decide +kernel))

def profile21_node13_cert : CutBound 7 := { lost := (rows 64 64 64 1 1 0 0), upper := (rows 7 35 13 106 114 32 64), lower := (rows 7 35 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 6, region := (rows 13 15 12 8 16 127 0), good := (rows 39 35 47 47 48 32 32) }] }

theorem profile21_node13 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,9] 6 98 profile21_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,9] 6 98 profile21_node13_cert).mp (by decide +kernel))

def profile21_node14_cert : CutBound 7 := { lost := (rows 96 64 64 2 2 0 0), upper := (rows 7 35 14 105 113 32 64), lower := (rows 7 35 14 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) },{ target := 5, region := (rows 5 2 4 8 16 0 127), good := (rows 71 67 79 72 80 64 64) },{ target := 6, region := (rows 13 15 12 8 16 127 0), good := (rows 39 35 47 47 48 32 32) }] }

theorem profile21_node14 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,10] 6 97 profile21_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,10] 6 97 profile21_node14_cert).mp (by decide +kernel))

def profile21_node15_cert : CutBound 7 := { lost := (rows 0 0 2 33 33 0 0), upper := (rows 7 35 37 74 90 32 64), lower := (rows 7 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 95 91 93 72 80 64 64) }] }

theorem profile21_node15 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,33] 6 74 profile21_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,33] 6 74 profile21_node15_cert).mp (by decide +kernel))

def profile21_node16_cert : CutBound 7 := { lost := (rows 32 0 1 34 34 0 0), upper := (rows 7 35 38 73 89 32 64), lower := (rows 7 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) },{ target := 5, region := (rows 5 2 4 15 23 0 127), good := (rows 95 91 95 72 80 64 64) }] }

theorem profile21_node16 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,34] 6 73 profile21_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,34] 6 73 profile21_node16_cert).mp (by decide +kernel))

def profile21_node17_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 7 35 44 75 83 32 64), lower := (rows 7 35 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 102 98 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 101 97 108 108 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 95 91 76 72 80 64 64) }] }

theorem profile21_node17 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,40] 6 67 profile21_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,40] 6 67 profile21_node17_cert).mp (by decide +kernel))

def profile21_node18_cert : CutBound 7 := { lost := (rows 32 0 34 1 1 0 0), upper := (rows 7 35 69 106 122 32 64), lower := (rows 7 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 126 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 71 69 72 80 64 64) }] }

theorem profile21_node18 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,65] 6 106 profile21_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,65] 6 106 profile21_node18_cert).mp (by decide +kernel))

def profile21_node19_cert : CutBound 7 := { lost := (rows 32 0 33 2 2 0 0), upper := (rows 7 35 70 105 121 32 64), lower := (rows 7 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 125 121 124 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile21_node19 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,66] 6 105 profile21_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,66] 6 105 profile21_node19_cert).mp (by decide +kernel))

def profile21_node20_cert : CutBound 7 := { lost := (rows 64 64 35 0 0 0 0), upper := (rows 7 35 76 107 115 32 64), lower := (rows 7 35 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 102 98 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 101 97 108 108 112 96 96) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 71 67 76 76 80 64 64) },{ target := 6, region := (rows 5 7 4 8 16 127 0), good := (rows 39 35 47 40 48 32 32) }] }

theorem profile21_node20 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,72] 6 99 profile21_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,72] 6 99 profile21_node20_cert).mp (by decide +kernel))

def profile21_node21_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 7 35 100 75 91 32 64), lower := (rows 7 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 95 91 68 72 80 64 64) }] }

theorem profile21_node21 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,96] 6 75 profile21_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33,96] 6 75 profile21_node21_cert).mp (by decide +kernel))

def profile21_node11_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node11 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,33] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile21_node11_route profile21_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node12
  · exact profile21_node13
  · exact profile21_node14
  · exact profile21_node15
  · exact profile21_node16
  · exact profile21_node17
  · exact profile21_node18
  · exact profile21_node19
  · exact profile21_node20
  · exact profile21_node21

def profile21_node23_cert : CutBound 7 := { lost := (rows 32 1 32 2 2 0 0), upper := (rows 7 42 7 105 113 32 64), lower := (rows 7 42 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 102 106 102 106 112 96 96) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 104 125 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 79 71 72 80 64 64) }] }

theorem profile21_node23 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,3] 6 97 profile21_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,3] 6 97 profile21_node23_cert).mp (by decide +kernel))

def profile21_node24_cert : CutBound 7 := { lost := (rows 0 1 2 32 32 0 0), upper := (rows 7 42 37 75 83 32 64), lower := (rows 7 42 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 102 106 100 106 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 104 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 74 93 72 80 64 64) }] }

theorem profile21_node24 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,33] 6 67 profile21_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,33] 6 67 profile21_node24_cert).mp (by decide +kernel))

def profile21_node25_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 7 42 38 73 81 32 64), lower := (rows 7 42 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 15 8 16 127 127), good := (rows 102 110 102 110 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 104 100 104 112 96 96) }] }

theorem profile21_node25 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,34] 6 65 profile21_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,34] 6 65 profile21_node25_cert).mp (by decide +kernel))

def profile21_node26_cert : CutBound 7 := { lost := (rows 32 1 34 0 0 0 0), upper := (rows 7 42 69 107 115 32 64), lower := (rows 7 42 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 102 106 100 106 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 104 101 104 112 96 96) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 79 69 72 80 64 64) }] }

theorem profile21_node26 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,65] 6 99 profile21_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,65] 6 99 profile21_node26_cert).mp (by decide +kernel))

def profile21_node27_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 7 42 70 105 113 32 64), lower := (rows 7 42 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 15 8 16 127 127), good := (rows 102 110 102 110 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 104 100 104 112 96 96) }] }

theorem profile21_node27 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,66] 6 97 profile21_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,66] 6 97 profile21_node27_cert).mp (by decide +kernel))

def profile21_node28_cert : CutBound 7 := { lost := (rows 0 1 3 32 32 0 0), upper := (rows 7 42 100 75 83 32 64), lower := (rows 7 42 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 102 110 100 110 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 108 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 74 68 72 80 64 64) }] }

theorem profile21_node28 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,96] 6 67 profile21_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40,96] 6 67 profile21_node28_cert).mp (by decide +kernel))

def profile21_node22_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node22_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node22 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,40] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node22_route profile21_node22_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node23
  · exact profile21_node24
  · exact profile21_node25
  · exact profile21_node26
  · exact profile21_node27
  · exact profile21_node28

def profile21_node30_cert : CutBound 7 := { lost := (rows 32 1 32 2 2 0 0), upper := (rows 7 98 7 105 121 32 64), lower := (rows 7 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 125 96 125 104 112 96 96) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile21_node30 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,3] 6 105 profile21_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,3] 6 105 profile21_node30_cert).mp (by decide +kernel))

def profile21_node32_cert : CutBound 7 := { lost := (rows 0 1 2 0 3 0 0), upper := (rows 7 98 13 11 112 32 64), lower := (rows 7 98 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) },{ target := 1, region := (rows 1 0 12 8 127 127 127), good := (rows 117 112 125 125 112 112 112) }] }

theorem profile21_node32 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,3] 6 96 profile21_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,3] 6 96 profile21_node32_cert).mp (by decide +kernel))

def profile21_node33_cert : CutBound 7 := { lost := (rows 0 1 2 2 1 0 0), upper := (rows 7 98 13 41 82 32 64), lower := (rows 7 98 13 41 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 126 122 114 114 114) },{ target := 1, region := (rows 1 0 13 13 16 127 127), good := (rows 109 96 109 109 112 96 96) }] }

theorem profile21_node33 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,33] 6 66 profile21_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,33] 6 66 profile21_node33_cert).mp (by decide +kernel))

def profile21_node34_cert : CutBound 7 := { lost := (rows 32 1 32 1 34 0 0), upper := (rows 7 98 13 42 81 32 64), lower := (rows 7 98 13 42 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 127), good := (rows 110 106 110 106 122 106 106) },{ target := 1, region := (rows 1 0 4 8 21 127 127), good := (rows 117 96 125 104 112 96 96) },{ target := 5, region := (rows 9 2 12 8 29 0 127), good := (rows 87 66 93 95 80 64 64) }] }

theorem profile21_node34 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,34] 6 65 profile21_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,34] 6 65 profile21_node34_cert).mp (by decide +kernel))

def profile21_node35_cert : CutBound 7 := { lost := (rows 0 1 2 3 0 0 0), upper := (rows 7 98 13 104 19 32 64), lower := (rows 7 98 13 104 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 127), good := (rows 110 106 110 106 122 106 106) },{ target := 1, region := (rows 1 0 5 127 16 127 127), good := (rows 109 104 109 104 120 104 104) }] }

theorem profile21_node35 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,96] 6 3 profile21_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9,96] 6 3 profile21_node35_cert).mp (by decide +kernel))

def profile21_node31_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node31_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node31 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,9] 6 (by decide) (choices 2) [3,33,34,96] profile21_node31_route profile21_node31_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node32
  · exact profile21_node33
  · exact profile21_node34
  · exact profile21_node35

def profile21_node36_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 7 98 14 105 113 32 64), lower := (rows 7 98 14 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 102 98 110 110 114 98 98) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 108 104 112 96 96) }] }

theorem profile21_node36 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,10] 6 97 profile21_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,10] 6 97 profile21_node36_cert).mp (by decide +kernel))

def profile21_node37_cert : CutBound 7 := { lost := (rows 0 1 2 32 32 0 0), upper := (rows 7 98 37 75 91 32 64), lower := (rows 7 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 93 72 80 64 64) }] }

theorem profile21_node37 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,33] 6 75 profile21_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,33] 6 75 profile21_node37_cert).mp (by decide +kernel))

def profile21_node38_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 7 98 38 73 89 32 64), lower := (rows 7 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 125 96 100 104 112 96 96) }] }

theorem profile21_node38 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,34] 6 73 profile21_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,34] 6 73 profile21_node38_cert).mp (by decide +kernel))

def profile21_node39_cert : CutBound 7 := { lost := (rows 0 1 3 32 32 0 0), upper := (rows 7 98 44 75 83 32 64), lower := (rows 7 98 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 102 98 110 110 114 98 98) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 101 96 108 108 112 96 96) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 76 72 80 64 64) }] }

theorem profile21_node39 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,40] 6 67 profile21_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,40] 6 67 profile21_node39_cert).mp (by decide +kernel))

def profile21_node40_cert : CutBound 7 := { lost := (rows 0 1 3 32 32 0 0), upper := (rows 7 98 100 11 27 32 64), lower := (rows 7 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 100 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile21_node40 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,96] 6 11 profile21_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96,96] 6 11 profile21_node40_cert).mp (by decide +kernel))

def profile21_node29_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node29_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node29 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6,96] 6 (by decide) (choices 2) [3,9,10,33,34,40,96] profile21_node29_route profile21_node29_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node30
  · exact profile21_node31
  · exact profile21_node36
  · exact profile21_node37
  · exact profile21_node38
  · exact profile21_node39
  · exact profile21_node40

def profile21_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node1 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [6] 6 (by decide) (choices 2) [9,33,40,96] profile21_node1_route profile21_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node2
  · exact profile21_node11
  · exact profile21_node22
  · exact profile21_node29

def profile21_node43_cert : CutBound 7 := { lost := (rows 64 64 96 1 1 0 0), upper := (rows 13 35 7 106 114 32 64), lower := (rows 13 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 124 122 126 104 112 96 96) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 77 71 71 72 80 64 64) },{ target := 6, region := (rows 9 15 15 8 16 127 0), good := (rows 47 39 39 47 48 32 32) }] }

theorem profile21_node43 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,3] 6 98 profile21_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,3] 6 98 profile21_node43_cert).mp (by decide +kernel))

def profile21_node44_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 13 35 37 74 82 32 64), lower := (rows 13 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 108 122 100 104 112 96 96) },{ target := 1, region := (rows 9 0 15 8 16 127 127), good := (rows 109 101 101 109 112 96 96) }] }

theorem profile21_node44 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,33] 6 66 profile21_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,33] 6 66 profile21_node44_cert).mp (by decide +kernel))

def profile21_node45_cert : CutBound 7 := { lost := (rows 32 0 1 32 32 0 0), upper := (rows 13 35 38 75 83 32 64), lower := (rows 13 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 108 102 102 104 112 96 96) },{ target := 5, region := (rows 5 2 4 14 22 0 127), good := (rows 93 91 95 72 80 64 64) }] }

theorem profile21_node45 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,34] 6 67 profile21_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,34] 6 67 profile21_node45_cert).mp (by decide +kernel))

def profile21_node46_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 13 35 69 106 114 32 64), lower := (rows 13 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 108 122 100 104 112 96 96) },{ target := 1, region := (rows 9 0 15 8 16 127 127), good := (rows 109 101 101 109 112 96 96) }] }

theorem profile21_node46 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,65] 6 98 profile21_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,65] 6 98 profile21_node46_cert).mp (by decide +kernel))

def profile21_node48_cert : CutBound 7 := { lost := (rows 32 0 33 32 3 0 0), upper := (rows 13 35 70 11 112 32 64), lower := (rows 13 35 70 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 127 127 127), good := (rows 124 118 118 126 112 112 112) },{ target := 1, region := (rows 1 0 4 8 127 127 127), good := (rows 125 113 116 121 112 112 112) },{ target := 5, region := (rows 15 2 14 14 16 0 127), good := (rows 77 79 79 79 80 64 64) }] }

theorem profile21_node48 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,3] 6 96 profile21_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,3] 6 96 profile21_node48_cert).mp (by decide +kernel))

def profile21_node49_cert : CutBound 7 := { lost := (rows 2 0 1 2 1 0 0), upper := (rows 13 35 70 41 82 32 64), lower := (rows 13 35 70 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 127 127), good := (rows 124 118 118 104 112 96 96) },{ target := 1, region := (rows 5 0 4 15 16 127 127), good := (rows 109 105 109 105 112 96 96) }] }

theorem profile21_node49 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,33] 6 66 profile21_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,33] 6 66 profile21_node49_cert).mp (by decide +kernel))

def profile21_node50_cert : CutBound 7 := { lost := (rows 32 0 33 1 34 0 0), upper := (rows 13 35 70 42 81 32 64), lower := (rows 13 35 70 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 14 16 127 127), good := (rows 108 110 110 110 112 96 96) },{ target := 1, region := (rows 1 0 4 8 19 127 127), good := (rows 125 113 116 120 112 96 96) },{ target := 5, region := (rows 9 2 14 8 27 0 127), good := (rows 93 87 86 95 80 64 64) }] }

theorem profile21_node50 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,34] 6 65 profile21_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,34] 6 65 profile21_node50_cert).mp (by decide +kernel))

def profile21_node51_cert : CutBound 7 := { lost := (rows 2 0 1 2 1 0 0), upper := (rows 13 35 70 73 50 32 64), lower := (rows 13 35 70 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 127 127), good := (rows 124 118 118 104 112 96 96) },{ target := 1, region := (rows 5 0 4 15 16 127 127), good := (rows 109 105 109 105 112 96 96) }] }

theorem profile21_node51 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,65] 6 34 profile21_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,65] 6 34 profile21_node51_cert).mp (by decide +kernel))

def profile21_node52_cert : CutBound 7 := { lost := (rows 32 0 33 33 2 0 0), upper := (rows 13 35 70 74 49 32 64), lower := (rows 13 35 70 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 14 16 127 127), good := (rows 108 110 110 110 112 96 96) },{ target := 1, region := (rows 1 0 4 8 19 127 127), good := (rows 125 113 116 120 112 96 96) },{ target := 5, region := (rows 15 2 14 14 16 0 127), good := (rows 77 79 79 79 80 64 64) }] }

theorem profile21_node52 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,66] 6 33 profile21_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,66] 6 33 profile21_node52_cert).mp (by decide +kernel))

def profile21_node53_cert : CutBound 7 := { lost := (rows 2 0 1 3 0 0 0), upper := (rows 13 35 70 104 19 32 64), lower := (rows 13 35 70 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 127 16 127 127), good := (rows 108 110 110 104 120 104 104) },{ target := 1, region := (rows 5 0 4 127 16 127 127), good := (rows 109 105 109 104 120 104 104) }] }

theorem profile21_node53 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,96] 6 3 profile21_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66,96] 6 3 profile21_node53_cert).mp (by decide +kernel))

def profile21_node47_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node47_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node47 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,66] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node47_route profile21_node47_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node48
  · exact profile21_node49
  · exact profile21_node50
  · exact profile21_node51
  · exact profile21_node52
  · exact profile21_node53

def profile21_node54_cert : CutBound 7 := { lost := (rows 2 0 3 32 32 0 0), upper := (rows 13 35 100 75 83 32 64), lower := (rows 13 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 108 102 100 108 116 100 100) },{ target := 1, region := (rows 9 0 127 8 16 127 127), good := (rows 109 101 100 109 116 100 100) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 77 91 68 72 80 64 64) }] }

theorem profile21_node54 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,96] 6 67 profile21_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33,96] 6 67 profile21_node54_cert).mp (by decide +kernel))

def profile21_node42_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node42_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node42 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,33] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node42_route profile21_node42_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node43
  · exact profile21_node44
  · exact profile21_node45
  · exact profile21_node46
  · exact profile21_node47
  · exact profile21_node54

def profile21_node57_cert : CutBound 7 := { lost := (rows 32 1 32 32 3 0 0), upper := (rows 13 98 7 11 112 32 64), lower := (rows 13 98 7 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 126 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 4 8 127 127 127), good := (rows 125 112 117 121 112 112 112) },{ target := 5, region := (rows 15 2 14 14 16 0 127), good := (rows 77 79 79 79 80 64 64) }] }

theorem profile21_node57 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,3] 6 96 profile21_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,3] 6 96 profile21_node57_cert).mp (by decide +kernel))

def profile21_node58_cert : CutBound 7 := { lost := (rows 2 1 0 2 1 0 0), upper := (rows 13 98 7 41 82 32 64), lower := (rows 13 98 7 41 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 126 114 118 122 114 114 114) },{ target := 1, region := (rows 5 0 4 13 16 127 127), good := (rows 109 96 109 105 112 96 96) }] }

theorem profile21_node58 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,33] 6 66 profile21_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,33] 6 66 profile21_node58_cert).mp (by decide +kernel))

def profile21_node59_cert : CutBound 7 := { lost := (rows 32 1 32 1 34 0 0), upper := (rows 13 98 7 42 81 32 64), lower := (rows 13 98 7 42 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 127), good := (rows 110 106 110 106 122 106 106) },{ target := 1, region := (rows 1 0 4 8 21 127 127), good := (rows 125 96 117 104 112 96 96) },{ target := 5, region := (rows 9 2 12 8 29 0 127), good := (rows 93 66 87 95 80 64 64) }] }

theorem profile21_node59 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,34] 6 65 profile21_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,34] 6 65 profile21_node59_cert).mp (by decide +kernel))

def profile21_node60_cert : CutBound 7 := { lost := (rows 2 1 0 3 0 0 0), upper := (rows 13 98 7 104 19 32 64), lower := (rows 13 98 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 127 16 127 127), good := (rows 110 106 110 106 122 106 106) },{ target := 1, region := (rows 5 0 4 127 16 127 127), good := (rows 109 104 109 104 120 104 104) }] }

theorem profile21_node60 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,96] 6 3 profile21_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3,96] 6 3 profile21_node60_cert).mp (by decide +kernel))

def profile21_node56_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node56_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node56 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,3] 6 (by decide) (choices 2) [3,33,34,96] profile21_node56_route profile21_node56_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node57
  · exact profile21_node58
  · exact profile21_node59
  · exact profile21_node60

def profile21_node61_cert : CutBound 7 := { lost := (rows 66 1 66 0 0 0 0), upper := (rows 13 98 37 75 83 32 64), lower := (rows 13 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 110 98 102 106 114 98 98) },{ target := 1, region := (rows 9 0 13 8 16 127 127), good := (rows 109 96 101 109 112 96 96) },{ target := 6, region := (rows 9 2 13 8 16 127 0), good := (rows 45 34 37 45 48 32 32) }] }

theorem profile21_node61 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,33] 6 67 profile21_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,33] 6 67 profile21_node61_cert).mp (by decide +kernel))

def profile21_node62_cert : CutBound 7 := { lost := (rows 32 1 1 32 32 0 0), upper := (rows 13 98 38 75 83 32 64), lower := (rows 13 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 110 102 102 110 118 102 102) },{ target := 5, region := (rows 5 2 4 12 20 0 127), good := (rows 93 66 95 72 80 64 64) }] }

theorem profile21_node62 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,34] 6 67 profile21_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,34] 6 67 profile21_node62_cert).mp (by decide +kernel))

def profile21_node63_cert : CutBound 7 := { lost := (rows 2 1 3 0 0 0 0), upper := (rows 13 98 100 11 19 32 64), lower := (rows 13 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 110 102 102 110 118 102 102) },{ target := 1, region := (rows 9 0 127 8 16 127 127), good := (rows 109 100 100 109 116 100 100) }] }

theorem profile21_node63 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,96] 6 3 profile21_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96,96] 6 3 profile21_node63_cert).mp (by decide +kernel))

def profile21_node55_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node55_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node55 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12,96] 6 (by decide) (choices 2) [3,33,34,96] profile21_node55_route profile21_node55_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node56
  · exact profile21_node61
  · exact profile21_node62
  · exact profile21_node63

def profile21_node41_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node41_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node41 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [12] 6 (by decide) (choices 2) [33,96] profile21_node41_route profile21_node41_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node42
  · exact profile21_node55

def profile21_node66_cert : CutBound 7 := { lost := (rows 0 0 0 3 3 0 0), upper := (rows 35 7 7 104 120 32 64), lower := (rows 35 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 125 120 120 120 120) }] }

theorem profile21_node66 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,3] 6 104 profile21_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,3] 6 104 profile21_node66_cert).mp (by decide +kernel))

def profile21_node67_cert : CutBound 7 := { lost := (rows 64 96 64 1 1 0 0), upper := (rows 35 7 13 106 114 32 64), lower := (rows 35 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 67 71 79 72 80 64 64) },{ target := 6, region := (rows 15 14 12 8 16 127 0), good := (rows 35 39 47 47 48 32 32) }] }

theorem profile21_node67 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,9] 6 98 profile21_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,9] 6 98 profile21_node67_cert).mp (by decide +kernel))

def profile21_node68_cert : CutBound 7 := { lost := (rows 64 64 64 2 2 0 0), upper := (rows 35 7 14 105 113 32 64), lower := (rows 35 7 14 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) },{ target := 6, region := (rows 15 14 12 8 16 127 0), good := (rows 35 39 47 47 48 32 32) }] }

theorem profile21_node68 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,10] 6 97 profile21_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,10] 6 97 profile21_node68_cert).mp (by decide +kernel))

def profile21_node69_cert : CutBound 7 := { lost := (rows 0 32 2 33 33 0 0), upper := (rows 35 7 37 74 90 32 64), lower := (rows 35 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 6 4 15 23 0 127), good := (rows 91 95 95 72 80 64 64) }] }

theorem profile21_node69 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,33] 6 74 profile21_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,33] 6 74 profile21_node69_cert).mp (by decide +kernel))

def profile21_node70_cert : CutBound 7 := { lost := (rows 0 0 1 34 34 0 0), upper := (rows 35 7 38 73 89 32 64), lower := (rows 35 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 91 95 94 72 80 64 64) }] }

theorem profile21_node70 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,34] 6 73 profile21_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,34] 6 73 profile21_node70_cert).mp (by decide +kernel))

def profile21_node71_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 35 7 44 75 83 32 64), lower := (rows 35 7 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 98 102 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 101 108 108 112 96 96) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 91 95 76 72 80 64 64) }] }

theorem profile21_node71 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,40] 6 67 profile21_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,40] 6 67 profile21_node71_cert).mp (by decide +kernel))

def profile21_node72_cert : CutBound 7 := { lost := (rows 0 32 34 1 1 0 0), upper := (rows 35 7 69 106 122 32 64), lower := (rows 35 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 126 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile21_node72 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,65] 6 106 profile21_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,65] 6 106 profile21_node72_cert).mp (by decide +kernel))

def profile21_node73_cert : CutBound 7 := { lost := (rows 0 32 33 2 2 0 0), upper := (rows 35 7 70 105 121 32 64), lower := (rows 35 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 125 124 104 112 96 96) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) }] }

theorem profile21_node73 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,66] 6 105 profile21_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,66] 6 105 profile21_node73_cert).mp (by decide +kernel))

def profile21_node74_cert : CutBound 7 := { lost := (rows 64 64 35 0 0 0 0), upper := (rows 35 7 76 107 115 32 64), lower := (rows 35 7 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 98 102 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 101 108 108 112 96 96) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 67 71 76 76 80 64 64) },{ target := 6, region := (rows 7 6 4 8 16 127 0), good := (rows 35 39 47 40 48 32 32) }] }

theorem profile21_node74 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,72] 6 99 profile21_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,72] 6 99 profile21_node74_cert).mp (by decide +kernel))

def profile21_node75_cert : CutBound 7 := { lost := (rows 0 0 3 32 32 0 0), upper := (rows 35 7 100 75 91 32 64), lower := (rows 35 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 11 19 0 127), good := (rows 91 95 68 72 80 64 64) }] }

theorem profile21_node75 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,96] 6 75 profile21_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5,96] 6 75 profile21_node75_cert).mp (by decide +kernel))

def profile21_node65_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node65_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node65 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,5] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile21_node65_route profile21_node65_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node66
  · exact profile21_node67
  · exact profile21_node68
  · exact profile21_node69
  · exact profile21_node70
  · exact profile21_node71
  · exact profile21_node72
  · exact profile21_node73
  · exact profile21_node74
  · exact profile21_node75

def profile21_node77_cert : CutBound 7 := { lost := (rows 64 64 96 2 2 0 0), upper := (rows 35 14 7 105 113 32 64), lower := (rows 35 14 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 121 124 125 104 112 96 96) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 71 78 71 72 80 64 64) },{ target := 6, region := (rows 15 10 15 8 16 127 0), good := (rows 39 47 39 47 48 32 32) }] }

theorem profile21_node77 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,3] 6 97 profile21_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,3] 6 97 profile21_node77_cert).mp (by decide +kernel))

def profile21_node78_cert : CutBound 7 := { lost := (rows 0 32 2 32 32 0 0), upper := (rows 35 14 37 75 83 32 64), lower := (rows 35 14 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 108 101 104 112 96 96) },{ target := 5, region := (rows 1 6 4 13 21 0 127), good := (rows 91 94 95 72 80 64 64) }] }

theorem profile21_node78 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,33] 6 67 profile21_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,33] 6 67 profile21_node78_cert).mp (by decide +kernel))

def profile21_node79_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 35 14 38 73 81 32 64), lower := (rows 35 14 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 15 8 16 127 127), good := (rows 102 110 102 110 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 108 100 104 112 96 96) }] }

theorem profile21_node79 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,34] 6 65 profile21_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,34] 6 65 profile21_node79_cert).mp (by decide +kernel))

def profile21_node81_cert : CutBound 7 := { lost := (rows 0 32 34 32 3 0 0), upper := (rows 35 14 69 11 112 32 64), lower := (rows 35 14 69 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 114 126 116 122 112 112 112) },{ target := 1, region := (rows 1 0 13 8 127 127 127), good := (rows 117 124 117 125 112 112 112) },{ target := 5, region := (rows 1 15 13 13 16 0 127), good := (rows 79 78 79 79 80 64 64) }] }

theorem profile21_node81 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,3] 6 96 profile21_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,3] 6 96 profile21_node81_cert).mp (by decide +kernel))

def profile21_node82_cert : CutBound 7 := { lost := (rows 0 32 34 2 33 0 0), upper := (rows 35 14 69 41 82 32 64), lower := (rows 35 14 69 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 19 127 127), good := (rows 114 126 116 120 112 96 96) },{ target := 1, region := (rows 1 0 13 13 16 127 127), good := (rows 109 108 109 109 112 96 96) },{ target := 5, region := (rows 1 10 13 8 27 0 127), good := (rows 87 94 85 95 80 64 64) }] }

theorem profile21_node82 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,33] 6 66 profile21_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,33] 6 66 profile21_node82_cert).mp (by decide +kernel))

def profile21_node83_cert : CutBound 7 := { lost := (rows 0 1 2 1 2 0 0), upper := (rows 35 14 69 42 81 32 64), lower := (rows 35 14 69 42 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 15 16 127 127), good := (rows 106 110 110 106 112 96 96) },{ target := 1, region := (rows 1 0 5 8 21 127 127), good := (rows 117 124 117 104 112 96 96) }] }

theorem profile21_node83 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,34] 6 65 profile21_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,34] 6 65 profile21_node83_cert).mp (by decide +kernel))

def profile21_node84_cert : CutBound 7 := { lost := (rows 0 32 34 34 1 0 0), upper := (rows 35 14 69 73 50 32 64), lower := (rows 35 14 69 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 19 127 127), good := (rows 114 126 116 120 112 96 96) },{ target := 1, region := (rows 1 0 13 13 16 127 127), good := (rows 109 108 109 109 112 96 96) },{ target := 5, region := (rows 1 15 13 13 16 0 127), good := (rows 79 78 79 79 80 64 64) }] }

theorem profile21_node84 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,65] 6 34 profile21_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,65] 6 34 profile21_node84_cert).mp (by decide +kernel))

def profile21_node85_cert : CutBound 7 := { lost := (rows 0 1 2 1 2 0 0), upper := (rows 35 14 69 74 49 32 64), lower := (rows 35 14 69 74 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 15 16 127 127), good := (rows 106 110 110 106 112 96 96) },{ target := 1, region := (rows 1 0 5 8 21 127 127), good := (rows 117 124 117 104 112 96 96) }] }

theorem profile21_node85 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,66] 6 33 profile21_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,66] 6 33 profile21_node85_cert).mp (by decide +kernel))

def profile21_node86_cert : CutBound 7 := { lost := (rows 0 1 2 3 0 0 0), upper := (rows 35 14 69 104 19 32 64), lower := (rows 35 14 69 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 106 110 110 104 120 104 104) },{ target := 1, region := (rows 1 0 5 127 16 127 127), good := (rows 109 108 109 104 120 104 104) }] }

theorem profile21_node86 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,96] 6 3 profile21_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65,96] 6 3 profile21_node86_cert).mp (by decide +kernel))

def profile21_node80_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node80_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node80 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,65] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node80_route profile21_node80_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node81
  · exact profile21_node82
  · exact profile21_node83
  · exact profile21_node84
  · exact profile21_node85
  · exact profile21_node86

def profile21_node87_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 35 14 70 105 113 32 64), lower := (rows 35 14 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 15 8 16 127 127), good := (rows 102 110 102 110 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 108 100 104 112 96 96) }] }

theorem profile21_node87 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,66] 6 97 profile21_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,66] 6 97 profile21_node87_cert).mp (by decide +kernel))

def profile21_node88_cert : CutBound 7 := { lost := (rows 0 1 3 32 32 0 0), upper := (rows 35 14 100 75 83 32 64), lower := (rows 35 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 102 110 100 110 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 108 100 108 116 100 100) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 91 78 68 72 80 64 64) }] }

theorem profile21_node88 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,96] 6 67 profile21_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12,96] 6 67 profile21_node88_cert).mp (by decide +kernel))

def profile21_node76_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node76_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node76 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,12] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node76_route profile21_node76_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node77
  · exact profile21_node78
  · exact profile21_node79
  · exact profile21_node80
  · exact profile21_node87
  · exact profile21_node88

def profile21_node89_cert : CutBound 7 := { lost := (rows 64 64 32 32 32 0 0), upper := (rows 35 35 79 79 95 32 64), lower := (rows 35 35 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) },{ target := 6, region := (rows 127 127 4 8 16 127 0), good := (rows 35 35 39 43 51 35 35) }] }

theorem profile21_node89 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,33] 6 79 profile21_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,33] 6 79 profile21_node89_cert).mp (by decide +kernel))

def profile21_node90_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 38 79 75 91 32 64), lower := (rows 35 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 70 68 72 80 64 64) }] }

theorem profile21_node90 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,36] 6 75 profile21_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,36] 6 75 profile21_node90_cert).mp (by decide +kernel))

def profile21_node92_cert : CutBound 7 := { lost := (rows 0 0 0 3 3 0 0), upper := (rows 35 67 7 108 124 32 64), lower := (rows 35 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 127 127), good := (rows 98 98 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 12 20 127 127), good := (rows 97 97 125 104 112 96 96) }] }

theorem profile21_node92 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,3] 6 108 profile21_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,3] 6 108 profile21_node92_cert).mp (by decide +kernel))

def profile21_node94_cert : CutBound 7 := { lost := (rows 0 32 32 32 3 0 0), upper := (rows 35 67 13 14 112 32 64), lower := (rows 35 67 13 14 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 114 114 124 126 112 112 112) },{ target := 1, region := (rows 1 0 4 8 127 127 127), good := (rows 113 113 125 124 112 112 112) },{ target := 5, region := (rows 1 7 7 15 16 0 127), good := (rows 79 79 79 78 80 64 64) }] }

theorem profile21_node94 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,6] 6 96 profile21_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,6] 6 96 profile21_node94_cert).mp (by decide +kernel))

def profile21_node95_cert : CutBound 7 := { lost := (rows 0 32 0 1 35 0 0), upper := (rows 35 67 13 42 84 32 64), lower := (rows 35 67 13 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 20 127 127), good := (rows 106 106 124 106 112 96 96) },{ target := 1, region := (rows 1 0 4 8 20 127 127), good := (rows 97 97 125 104 112 96 96) },{ target := 5, region := (rows 1 7 4 8 20 0 127), good := (rows 67 67 95 74 80 64 64) }] }

theorem profile21_node95 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,34] 6 68 profile21_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,34] 6 68 profile21_node95_cert).mp (by decide +kernel))

def profile21_node96_cert : CutBound 7 := { lost := (rows 0 0 2 3 1 0 0), upper := (rows 35 67 13 44 82 32 64), lower := (rows 35 67 13 44 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 127 127), good := (rows 114 114 124 108 112 96 96) },{ target := 1, region := (rows 1 0 7 15 16 127 127), good := (rows 109 109 109 108 112 96 96) }] }

theorem profile21_node96 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,36] 6 66 profile21_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,36] 6 66 profile21_node96_cert).mp (by decide +kernel))

def profile21_node97_cert : CutBound 7 := { lost := (rows 0 32 32 33 3 0 0), upper := (rows 35 67 13 74 52 32 64), lower := (rows 35 67 13 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 20 127 127), good := (rows 106 106 124 106 112 96 96) },{ target := 1, region := (rows 1 0 4 8 20 127 127), good := (rows 97 97 125 104 112 96 96) },{ target := 5, region := (rows 1 7 7 15 16 0 127), good := (rows 79 79 79 78 80 64 64) }] }

theorem profile21_node97 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,66] 6 36 profile21_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,66] 6 36 profile21_node97_cert).mp (by decide +kernel))

def profile21_node98_cert : CutBound 7 := { lost := (rows 0 0 2 3 1 0 0), upper := (rows 35 67 13 76 50 32 64), lower := (rows 35 67 13 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 127 127), good := (rows 114 114 124 108 112 96 96) },{ target := 1, region := (rows 1 0 7 15 16 127 127), good := (rows 109 109 109 108 112 96 96) }] }

theorem profile21_node98 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,68] 6 34 profile21_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,68] 6 34 profile21_node98_cert).mp (by decide +kernel))

def profile21_node99_cert : CutBound 7 := { lost := (rows 0 32 2 3 32 0 0), upper := (rows 35 67 13 104 22 32 64), lower := (rows 35 67 13 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 16 127 127), good := (rows 106 106 108 104 120 104 104) },{ target := 1, region := (rows 1 0 7 127 16 127 127), good := (rows 109 109 109 104 120 104 104) },{ target := 5, region := (rows 1 7 4 8 20 0 127), good := (rows 67 67 95 72 80 64 64) }] }

theorem profile21_node99 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,96] 6 6 profile21_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9,96] 6 6 profile21_node99_cert).mp (by decide +kernel))

def profile21_node93_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node93_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node93 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,9] 6 (by decide) (choices 2) [6,34,36,66,68,96] profile21_node93_route profile21_node93_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node94
  · exact profile21_node95
  · exact profile21_node96
  · exact profile21_node97
  · exact profile21_node98
  · exact profile21_node99

def profile21_node101_cert : CutBound 7 := { lost := (rows 0 32 32 32 3 0 0), upper := (rows 35 67 14 13 112 32 64), lower := (rows 35 67 14 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 114 114 126 124 112 112 112) },{ target := 1, region := (rows 1 0 4 8 127 127 127), good := (rows 113 113 124 125 112 112 112) },{ target := 5, region := (rows 1 11 15 11 16 0 127), good := (rows 79 79 78 79 80 64 64) }] }

theorem profile21_node101 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,5] 6 96 profile21_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,5] 6 96 profile21_node101_cert).mp (by decide +kernel))

def profile21_node102_cert : CutBound 7 := { lost := (rows 0 32 32 2 35 0 0), upper := (rows 35 67 14 41 84 32 64), lower := (rows 35 67 14 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 20 127 127), good := (rows 98 98 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 20 127 127), good := (rows 105 105 124 105 112 96 96) },{ target := 5, region := (rows 1 11 12 8 28 0 127), good := (rows 67 67 94 95 80 64 64) }] }

theorem profile21_node102 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,33] 6 68 profile21_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,33] 6 68 profile21_node102_cert).mp (by decide +kernel))

def profile21_node103_cert : CutBound 7 := { lost := (rows 0 0 1 3 2 0 0), upper := (rows 35 67 14 44 81 32 64), lower := (rows 35 67 14 44 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 15 16 127 127), good := (rows 110 110 110 108 112 96 96) },{ target := 1, region := (rows 1 0 4 12 19 127 127), good := (rows 113 113 124 108 112 96 96) }] }

theorem profile21_node103 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,36] 6 65 profile21_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,36] 6 65 profile21_node103_cert).mp (by decide +kernel))

def profile21_node104_cert : CutBound 7 := { lost := (rows 0 32 32 34 3 0 0), upper := (rows 35 67 14 73 52 32 64), lower := (rows 35 67 14 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 20 127 127), good := (rows 98 98 126 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 20 127 127), good := (rows 105 105 124 105 112 96 96) },{ target := 5, region := (rows 1 11 15 11 16 0 127), good := (rows 79 79 78 79 80 64 64) }] }

theorem profile21_node104 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,65] 6 36 profile21_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,65] 6 36 profile21_node104_cert).mp (by decide +kernel))

def profile21_node105_cert : CutBound 7 := { lost := (rows 0 0 1 3 2 0 0), upper := (rows 35 67 14 76 49 32 64), lower := (rows 35 67 14 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 15 16 127 127), good := (rows 110 110 110 108 112 96 96) },{ target := 1, region := (rows 1 0 4 12 19 127 127), good := (rows 113 113 124 108 112 96 96) }] }

theorem profile21_node105 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,68] 6 33 profile21_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,68] 6 33 profile21_node105_cert).mp (by decide +kernel))

def profile21_node106_cert : CutBound 7 := { lost := (rows 0 32 1 3 0 0 0), upper := (rows 35 67 14 104 21 32 64), lower := (rows 35 67 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 127 16 127 127), good := (rows 110 110 110 104 120 104 104) },{ target := 1, region := (rows 1 0 4 127 16 127 127), good := (rows 105 105 108 104 120 104 104) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 78 72 80 64 64) }] }

theorem profile21_node106 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,96] 6 5 profile21_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10,96] 6 5 profile21_node106_cert).mp (by decide +kernel))

def profile21_node100_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node100_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node100 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,10] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile21_node100_route profile21_node100_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node101
  · exact profile21_node102
  · exact profile21_node103
  · exact profile21_node104
  · exact profile21_node105
  · exact profile21_node106

def profile21_node107_cert : CutBound 7 := { lost := (rows 0 32 2 32 32 0 0), upper := (rows 35 67 37 78 94 32 64), lower := (rows 35 67 37 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 4 12 20 0 127), good := (rows 67 67 95 72 80 64 64) }] }

theorem profile21_node107 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,33] 6 78 profile21_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,33] 6 78 profile21_node107_cert).mp (by decide +kernel))

def profile21_node108_cert : CutBound 7 := { lost := (rows 64 32 65 0 0 0 0), upper := (rows 35 67 38 77 93 32 64), lower := (rows 35 67 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 70 72 80 64 64) },{ target := 6, region := (rows 7 2 7 8 16 127 0), good := (rows 39 39 39 40 48 32 32) }] }

theorem profile21_node108 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,34] 6 77 profile21_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,34] 6 77 profile21_node108_cert).mp (by decide +kernel))

def profile21_node109_cert : CutBound 7 := { lost := (rows 64 32 67 0 0 0 0), upper := (rows 35 67 44 79 87 32 64), lower := (rows 35 67 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 98 98 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 97 108 108 112 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 76 72 80 64 64) },{ target := 6, region := (rows 3 2 12 8 16 127 0), good := (rows 35 35 44 44 48 32 32) }] }

theorem profile21_node109 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,40] 6 71 profile21_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,40] 6 71 profile21_node109_cert).mp (by decide +kernel))

def profile21_node110_cert : CutBound 7 := { lost := (rows 64 32 34 0 0 0 0), upper := (rows 35 67 69 46 62 32 64), lower := (rows 35 67 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 101 101 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 37 40 48 32 32) }] }

theorem profile21_node110 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,65] 6 46 profile21_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,65] 6 46 profile21_node110_cert).mp (by decide +kernel))

def profile21_node111_cert : CutBound 7 := { lost := (rows 64 32 33 64 64 0 0), upper := (rows 35 67 70 45 61 32 64), lower := (rows 35 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 102 102 104 112 96 96) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) },{ target := 6, region := (rows 7 2 4 12 20 127 0), good := (rows 35 35 63 40 48 32 32) }] }

theorem profile21_node111 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,66] 6 45 profile21_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,66] 6 45 profile21_node111_cert).mp (by decide +kernel))

def profile21_node112_cert : CutBound 7 := { lost := (rows 0 32 35 0 0 0 0), upper := (rows 35 67 76 47 55 32 64), lower := (rows 35 67 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 98 98 108 108 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 97 108 108 112 96 96) },{ target := 5, region := (rows 1 3 12 8 16 0 127), good := (rows 67 67 76 76 80 64 64) }] }

theorem profile21_node112 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,72] 6 39 profile21_node112_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,72] 6 39 profile21_node112_cert).mp (by decide +kernel))

def profile21_node113_cert : CutBound 7 := { lost := (rows 64 32 3 0 0 0 0), upper := (rows 35 67 100 15 31 32 64), lower := (rows 35 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 101 100 108 116 100 100) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 127 0), good := (rows 35 35 36 40 48 32 32) }] }

theorem profile21_node113 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,96] 6 15 profile21_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65,96] 6 15 profile21_node113_cert).mp (by decide +kernel))

def profile21_node91_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node91_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node91 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,65] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile21_node91_route profile21_node91_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node92
  · exact profile21_node93
  · exact profile21_node100
  · exact profile21_node107
  · exact profile21_node108
  · exact profile21_node109
  · exact profile21_node110
  · exact profile21_node111
  · exact profile21_node112
  · exact profile21_node113

def profile21_node115_cert : CutBound 7 := { lost := (rows 0 33 32 2 2 0 0), upper := (rows 35 70 7 105 121 32 64), lower := (rows 35 70 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 13 21 127 127), good := (rows 121 124 125 104 112 96 96) },{ target := 5, region := (rows 1 7 5 8 16 0 127), good := (rows 71 70 71 72 80 64 64) }] }

theorem profile21_node115 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,3] 6 105 profile21_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,3] 6 105 profile21_node115_cert).mp (by decide +kernel))

def profile21_node117_cert : CutBound 7 := { lost := (rows 0 1 2 0 3 0 0), upper := (rows 35 70 13 11 112 32 64), lower := (rows 35 70 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 126 122 112 112 112) },{ target := 1, region := (rows 1 0 12 8 127 127 127), good := (rows 113 116 125 125 112 112 112) }] }

theorem profile21_node117 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,3] 6 96 profile21_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,3] 6 96 profile21_node117_cert).mp (by decide +kernel))

def profile21_node118_cert : CutBound 7 := { lost := (rows 0 1 2 2 1 0 0), upper := (rows 35 70 13 41 82 32 64), lower := (rows 35 70 13 41 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 127 127), good := (rows 114 118 126 120 112 96 96) },{ target := 1, region := (rows 1 0 13 13 16 127 127), good := (rows 109 108 109 109 112 96 96) }] }

theorem profile21_node118 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,33] 6 66 profile21_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,33] 6 66 profile21_node118_cert).mp (by decide +kernel))

def profile21_node119_cert : CutBound 7 := { lost := (rows 0 33 0 1 34 0 0), upper := (rows 35 70 13 42 81 32 64), lower := (rows 35 70 13 42 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 15 16 127 127), good := (rows 106 110 110 106 112 96 96) },{ target := 1, region := (rows 1 0 4 8 21 127 127), good := (rows 113 116 125 104 112 96 96) },{ target := 5, region := (rows 1 6 4 8 21 0 127), good := (rows 83 86 95 74 80 64 64) }] }

theorem profile21_node119 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,34] 6 65 profile21_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,34] 6 65 profile21_node119_cert).mp (by decide +kernel))

def profile21_node120_cert : CutBound 7 := { lost := (rows 0 1 2 2 1 0 0), upper := (rows 35 70 13 73 50 32 64), lower := (rows 35 70 13 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 127 127), good := (rows 114 118 126 120 112 96 96) },{ target := 1, region := (rows 1 0 13 13 16 127 127), good := (rows 109 108 109 109 112 96 96) }] }

theorem profile21_node120 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,65] 6 34 profile21_node120_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,65] 6 34 profile21_node120_cert).mp (by decide +kernel))

def profile21_node121_cert : CutBound 7 := { lost := (rows 0 33 32 33 2 0 0), upper := (rows 35 70 13 74 49 32 64), lower := (rows 35 70 13 74 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 15 16 127 127), good := (rows 106 110 110 106 112 96 96) },{ target := 1, region := (rows 1 0 4 8 21 127 127), good := (rows 113 116 125 104 112 96 96) },{ target := 5, region := (rows 1 7 5 15 16 0 127), good := (rows 79 78 79 74 80 64 64) }] }

theorem profile21_node121 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,66] 6 33 profile21_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,66] 6 33 profile21_node121_cert).mp (by decide +kernel))

def profile21_node122_cert : CutBound 7 := { lost := (rows 0 1 2 3 0 0 0), upper := (rows 35 70 13 104 19 32 64), lower := (rows 35 70 13 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 106 110 110 104 120 104 104) },{ target := 1, region := (rows 1 0 5 127 16 127 127), good := (rows 109 108 109 104 120 104 104) }] }

theorem profile21_node122 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,96] 6 3 profile21_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9,96] 6 3 profile21_node122_cert).mp (by decide +kernel))

def profile21_node116_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node116_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node116 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,9] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node116_route profile21_node116_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node117
  · exact profile21_node118
  · exact profile21_node119
  · exact profile21_node120
  · exact profile21_node121
  · exact profile21_node122

def profile21_node123_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 35 70 14 105 113 32 64), lower := (rows 35 70 14 8 16 32 64), losses := [{ target := 0, region := (rows 0 14 12 8 16 127 127), good := (rows 98 102 110 110 112 96 96) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 100 108 104 112 96 96) }] }

theorem profile21_node123 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,10] 6 97 profile21_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,10] 6 97 profile21_node123_cert).mp (by decide +kernel))

def profile21_node124_cert : CutBound 7 := { lost := (rows 0 33 2 32 32 0 0), upper := (rows 35 70 37 75 91 32 64), lower := (rows 35 70 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 100 101 104 112 96 96) },{ target := 5, region := (rows 1 6 4 13 21 0 127), good := (rows 91 94 95 72 80 64 64) }] }

theorem profile21_node124 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,33] 6 75 profile21_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,33] 6 75 profile21_node124_cert).mp (by decide +kernel))

def profile21_node125_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 35 70 38 73 89 32 64), lower := (rows 35 70 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 100 100 104 112 96 96) }] }

theorem profile21_node125 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,34] 6 73 profile21_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,34] 6 73 profile21_node125_cert).mp (by decide +kernel))

def profile21_node126_cert : CutBound 7 := { lost := (rows 0 33 3 32 32 0 0), upper := (rows 35 70 44 75 83 32 64), lower := (rows 35 70 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 14 12 8 16 127 127), good := (rows 98 102 110 110 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 100 108 108 112 96 96) },{ target := 5, region := (rows 1 6 4 9 17 0 127), good := (rows 91 70 78 72 80 64 64) }] }

theorem profile21_node126 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,40] 6 67 profile21_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,40] 6 67 profile21_node126_cert).mp (by decide +kernel))

def profile21_node127_cert : CutBound 7 := { lost := (rows 0 33 34 0 0 0 0), upper := (rows 35 70 69 43 59 32 64), lower := (rows 35 70 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 101 100 101 104 112 96 96) },{ target := 5, region := (rows 1 7 5 8 16 0 127), good := (rows 71 70 71 72 80 64 64) }] }

theorem profile21_node127 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,65] 6 43 profile21_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,65] 6 43 profile21_node127_cert).mp (by decide +kernel))

def profile21_node128_cert : CutBound 7 := { lost := (rows 0 1 1 2 2 0 0), upper := (rows 35 70 70 41 57 32 64), lower := (rows 35 70 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 4 9 17 127 127), good := (rows 121 100 100 104 112 96 96) }] }

theorem profile21_node128 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,66] 6 41 profile21_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,66] 6 41 profile21_node128_cert).mp (by decide +kernel))

def profile21_node129_cert : CutBound 7 := { lost := (rows 0 33 35 0 0 0 0), upper := (rows 35 70 76 43 51 32 64), lower := (rows 35 70 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 14 12 8 16 127 127), good := (rows 98 102 110 110 112 96 96) },{ target := 1, region := (rows 1 0 12 8 16 127 127), good := (rows 97 100 108 108 112 96 96) },{ target := 5, region := (rows 1 14 12 8 16 0 127), good := (rows 67 70 78 78 80 64 64) }] }

theorem profile21_node129 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,72] 6 35 profile21_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,72] 6 35 profile21_node129_cert).mp (by decide +kernel))

def profile21_node130_cert : CutBound 7 := { lost := (rows 0 33 3 32 32 0 0), upper := (rows 35 70 100 11 27 32 64), lower := (rows 35 70 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 100 100 108 116 100 100) },{ target := 5, region := (rows 1 6 4 9 17 0 127), good := (rows 91 70 70 72 80 64 64) }] }

theorem profile21_node130 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,96] 6 11 profile21_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68,96] 6 11 profile21_node130_cert).mp (by decide +kernel))


#print axioms profile21_node130
end Delivery.SmallBudgetTenFinite7
