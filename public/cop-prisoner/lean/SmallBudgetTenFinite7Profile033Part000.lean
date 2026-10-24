import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile33_node3_cert : CutBound 7 := { lost := (rows 32 32 32 17 0 0 0), upper := (rows 7 19 21 104 112 96 64), lower := (rows 7 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 109 104 104 104 104) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile33_node3 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,17] 6 96 profile33_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,17] 6 96 profile33_node3_cert).mp (by decide +kernel))

def profile33_node5_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 7 19 37 56 80 96 64), lower := (rows 7 19 37 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile33_node5 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,48] 6 64 profile33_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,48] 6 64 profile33_node5_cert).mp (by decide +kernel))

def profile33_node6_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 7 19 37 88 112 96 64), lower := (rows 7 19 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile33_node6 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,80] 6 96 profile33_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,80] 6 96 profile33_node6_cert).mp (by decide +kernel))

def profile33_node7_cert : CutBound 7 := { lost := (rows 32 32 0 17 0 0 0), upper := (rows 7 19 37 104 80 112 64), lower := (rows 7 19 37 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 79 67 109 104 64 104 64) },{ target := 5, region := (rows 5 7 4 8 127 0 127), good := (rows 87 83 87 88 80 80 80) }] }

theorem profile33_node7 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,96] 6 80 profile33_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33,96] 6 80 profile33_node7_cert).mp (by decide +kernel))

def profile33_node4_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node4_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node4 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,33] 6 (by decide) (choices 2) [48,80,96] profile33_node4_route profile33_node4_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node5
  · exact profile33_node6
  · exact profile33_node7

def profile33_node8_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 7 19 52 105 113 97 64), lower := (rows 7 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 111 107 100 72 64 96 64) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 71 83 87 72 80 64 64) }] }

theorem profile33_node8 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,48] 6 97 profile33_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,48] 6 97 profile33_node8_cert).mp (by decide +kernel))

def profile33_node9_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 7 19 69 120 112 112 64), lower := (rows 7 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile33_node9 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,65] 6 112 profile33_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,65] 6 112 profile33_node9_cert).mp (by decide +kernel))

def profile33_node10_cert : CutBound 7 := { lost := (rows 32 32 33 16 0 0 0), upper := (rows 7 19 84 105 113 97 64), lower := (rows 7 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 86 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 111 107 68 72 64 96 64) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile33_node10 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,80] 6 97 profile33_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,80] 6 97 profile33_node10_cert).mp (by decide +kernel))

def profile33_node12_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 7 19 100 25 112 96 64), lower := (rows 7 19 100 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 109 100 100 100) }] }

theorem profile33_node12 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,17] 6 96 profile33_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,17] 6 96 profile33_node12_cert).mp (by decide +kernel))

def profile33_node13_cert : CutBound 7 := { lost := (rows 32 32 17 0 0 0 0), upper := (rows 7 19 100 41 80 112 64), lower := (rows 7 19 100 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 44 8 0 32 127), good := (rows 71 67 100 109 64 100 64) },{ target := 5, region := (rows 5 15 4 8 127 0 127), good := (rows 87 83 87 91 80 80 80) }] }

theorem profile33_node13 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,33] 6 80 profile33_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,33] 6 80 profile33_node13_cert).mp (by decide +kernel))

def profile33_node14_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 7 19 100 56 81 97 64), lower := (rows 7 19 100 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 44 8 16 32 127), good := (rows 70 82 100 124 80 100 64) },{ target := 4, region := (rows 3 2 47 8 0 35 127), good := (rows 103 103 100 108 64 100 64) }] }

theorem profile33_node14 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,48] 6 65 profile33_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,48] 6 65 profile33_node14_cert).mp (by decide +kernel))

def profile33_node15_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 7 19 100 73 48 48 64), lower := (rows 7 19 100 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 36 11 0 32 127), good := (rows 79 75 100 73 64 100 64) }] }

theorem profile33_node15 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,65] 6 48 profile33_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,65] 6 48 profile33_node15_cert).mp (by decide +kernel))

def profile33_node16_cert : CutBound 7 := { lost := (rows 16 0 17 1 0 0 0), upper := (rows 7 19 100 88 49 33 64), lower := (rows 7 19 100 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 26 16 32 127), good := (rows 78 90 100 88 88 100 64) },{ target := 4, region := (rows 3 2 39 8 0 35 127), good := (rows 103 103 100 72 64 100 64) }] }

theorem profile33_node16 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,80] 6 33 profile33_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,80] 6 33 profile33_node16_cert).mp (by decide +kernel))

def profile33_node17_cert : CutBound 7 := { lost := (rows 0 0 17 17 0 0 0), upper := (rows 7 19 100 104 17 49 64), lower := (rows 7 19 100 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 44 44 16 32 127), good := (rows 78 82 108 108 80 108 64) },{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 79 67 108 108 64 108 64) }] }

theorem profile33_node17 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,96] 6 17 profile33_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96,96] 6 17 profile33_node17_cert).mp (by decide +kernel))

def profile33_node11_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node11_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node11 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17,96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node11_route profile33_node11_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node12
  · exact profile33_node13
  · exact profile33_node14
  · exact profile33_node15
  · exact profile33_node16
  · exact profile33_node17

def profile33_node2_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node2_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node2 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,17] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node2_route profile33_node2_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node3
  · exact profile33_node4
  · exact profile33_node8
  · exact profile33_node9
  · exact profile33_node10
  · exact profile33_node11

def profile33_node19_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 7 50 21 105 113 97 64), lower := (rows 7 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 111 98 109 72 64 96 64) },{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 87 85 72 80 64 64) }] }

theorem profile33_node19 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,17] 6 97 profile33_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,17] 6 97 profile33_node19_cert).mp (by decide +kernel))

def profile33_node20_cert : CutBound 7 := { lost := (rows 0 1 1 16 0 0 0), upper := (rows 7 50 52 73 81 97 64), lower := (rows 7 50 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 127), good := (rows 70 118 118 72 80 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 100 72 64 96 64) }] }

theorem profile33_node20 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,48] 6 65 profile33_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,48] 6 65 profile33_node20_cert).mp (by decide +kernel))

def profile33_node21_cert : CutBound 7 := { lost := (rows 48 0 48 0 0 0 0), upper := (rows 7 50 69 121 113 113 64), lower := (rows 7 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 87 69 72 80 64 64) }] }

theorem profile33_node21 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,65] 6 113 profile33_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,65] 6 113 profile33_node21_cert).mp (by decide +kernel))

def profile33_node22_cert : CutBound 7 := { lost := (rows 32 0 33 16 0 0 0), upper := (rows 7 50 84 105 113 97 64), lower := (rows 7 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 98 68 72 64 96 64) },{ target := 5, region := (rows 3 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile33_node22 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,80] 6 97 profile33_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48,80] 6 97 profile33_node22_cert).mp (by decide +kernel))

def profile33_node18_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node18_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node18 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,48] 6 (by decide) (choices 2) [17,48,65,80] profile33_node18_route profile33_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile33_node19
  · exact profile33_node20
  · exact profile33_node21
  · exact profile33_node22

def profile33_node23_cert : CutBound 7 := { lost := (rows 48 48 0 0 0 0 0), upper := (rows 7 67 117 121 113 113 64), lower := (rows 7 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 32 127), good := (rows 71 67 71 72 64 96 64) },{ target := 5, region := (rows 5 7 4 8 16 0 127), good := (rows 71 67 71 72 80 64 64) }] }

theorem profile33_node23 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,65] 6 113 profile33_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,65] 6 113 profile33_node23_cert).mp (by decide +kernel))

def profile33_node25_cert : CutBound 7 := { lost := (rows 32 33 32 16 0 0 0), upper := (rows 7 82 21 105 113 97 64), lower := (rows 7 82 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 16 32 127), good := (rows 70 82 86 72 82 96 64) },{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 111 66 109 72 64 96 64) },{ target := 5, region := (rows 23 22 22 8 16 0 127), good := (rows 71 87 87 72 87 64 64) }] }

theorem profile33_node25 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,17] 6 97 profile33_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,17] 6 97 profile33_node25_cert).mp (by decide +kernel))

def profile33_node27_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 7 82 37 25 112 96 64), lower := (rows 7 82 37 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 3 2 15 8 0 127 127), good := (rows 103 103 101 109 96 96 96) }] }

theorem profile33_node27 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,17] 6 96 profile33_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,17] 6 96 profile33_node27_cert).mp (by decide +kernel))

def profile33_node28_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 7 82 37 41 80 112 64), lower := (rows 7 82 37 41 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 1 2 12 12 0 32 127), good := (rows 79 66 109 109 64 96 64) }] }

theorem profile33_node28 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,33] 6 80 profile33_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,33] 6 80 profile33_node28_cert).mp (by decide +kernel))

def profile33_node29_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 7 82 37 56 81 97 64), lower := (rows 7 82 37 56 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 8 16 32 127), good := (rows 70 82 100 122 82 96 64) },{ target := 4, region := (rows 3 2 7 8 0 39 127), good := (rows 103 103 101 104 64 96 64) }] }

theorem profile33_node29 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,48] 6 65 profile33_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,48] 6 65 profile33_node29_cert).mp (by decide +kernel))

def profile33_node30_cert : CutBound 7 := { lost := (rows 0 33 0 48 0 0 0), upper := (rows 7 82 37 73 48 48 64), lower := (rows 7 82 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 1 2 4 13 0 32 127), good := (rows 79 66 109 73 64 96 64) },{ target := 5, region := (rows 1 18 4 13 16 0 127), good := (rows 79 82 77 73 82 64 64) }] }

theorem profile33_node30 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,65] 6 48 profile33_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,65] 6 48 profile33_node30_cert).mp (by decide +kernel))

def profile33_node31_cert : CutBound 7 := { lost := (rows 16 1 16 1 0 0 0), upper := (rows 7 82 37 88 49 33 64), lower := (rows 7 82 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 78 90 100 90 90 96 64) },{ target := 4, region := (rows 3 2 7 8 0 39 127), good := (rows 103 103 101 72 64 96 64) }] }

theorem profile33_node31 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,80] 6 33 profile33_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,80] 6 33 profile33_node31_cert).mp (by decide +kernel))

def profile33_node32_cert : CutBound 7 := { lost := (rows 0 1 0 17 0 0 0), upper := (rows 7 82 37 104 17 49 64), lower := (rows 7 82 37 104 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 44 16 32 127), good := (rows 78 82 108 104 82 104 64) },{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 79 66 109 104 64 104 64) }] }

theorem profile33_node32 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,96] 6 17 profile33_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33,96] 6 17 profile33_node32_cert).mp (by decide +kernel))

def profile33_node26_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node26_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node26 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,33] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node26_route profile33_node26_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node27
  · exact profile33_node28
  · exact profile33_node29
  · exact profile33_node30
  · exact profile33_node31
  · exact profile33_node32

def profile33_node33_cert : CutBound 7 := { lost := (rows 32 33 0 16 0 0 0), upper := (rows 7 82 52 105 113 97 64), lower := (rows 7 82 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 16 32 127), good := (rows 70 82 118 72 82 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 100 72 64 96 64) },{ target := 5, region := (rows 5 22 4 8 16 0 127), good := (rows 71 82 87 72 82 64 64) }] }

theorem profile33_node33 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,48] 6 97 profile33_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,48] 6 97 profile33_node33_cert).mp (by decide +kernel))

def profile33_node34_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 7 82 69 57 49 49 64), lower := (rows 7 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 70 82 68 72 82 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile33_node34 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,65] 6 49 profile33_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,65] 6 49 profile33_node34_cert).mp (by decide +kernel))

def profile33_node35_cert : CutBound 7 := { lost := (rows 0 1 1 16 0 0 0), upper := (rows 7 82 84 41 49 33 64), lower := (rows 7 82 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 111 66 68 72 64 96 64) }] }

theorem profile33_node35 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,80] 6 33 profile33_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,80] 6 33 profile33_node35_cert).mp (by decide +kernel))

def profile33_node36_cert : CutBound 7 := { lost := (rows 0 1 17 0 0 0 0), upper := (rows 7 82 100 57 49 49 64), lower := (rows 7 82 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 36 8 16 32 127), good := (rows 70 82 100 72 82 100 64) },{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 71 66 100 72 64 100 64) }] }

theorem profile33_node36 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,96] 6 49 profile33_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80,96] 6 49 profile33_node36_cert).mp (by decide +kernel))

def profile33_node24_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node24_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node24 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6,80] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node24_route profile33_node24_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node25
  · exact profile33_node26
  · exact profile33_node33
  · exact profile33_node34
  · exact profile33_node35
  · exact profile33_node36

def profile33_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node1 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [6] 6 (by decide) (choices 2) [17,48,65,80] profile33_node1_route profile33_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile33_node2
  · exact profile33_node18
  · exact profile33_node23
  · exact profile33_node24

def profile33_node39_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 19 7 21 104 112 96 64), lower := (rows 19 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 6 4 127 0 127 127), good := (rows 107 111 111 104 104 104 104) }] }

theorem profile33_node39 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,17] 6 96 profile33_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,17] 6 96 profile33_node39_cert).mp (by decide +kernel))

def profile33_node40_cert : CutBound 7 := { lost := (rows 0 48 0 1 0 0 0), upper := (rows 19 7 37 120 112 112 64), lower := (rows 19 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 71 103 72 64 96 64) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 83 71 71 72 80 64 64) }] }

theorem profile33_node40 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,33] 6 112 profile33_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,33] 6 112 profile33_node40_cert).mp (by decide +kernel))

def profile33_node41_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 19 7 52 105 113 97 64), lower := (rows 19 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 107 111 100 72 64 96 64) },{ target := 5, region := (rows 5 6 4 8 16 0 127), good := (rows 83 71 87 72 80 64 64) }] }

theorem profile33_node41 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,48] 6 97 profile33_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,48] 6 97 profile33_node41_cert).mp (by decide +kernel))

def profile33_node42_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 19 7 69 120 112 112 64), lower := (rows 19 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile33_node42 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,65] 6 112 profile33_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,65] 6 112 profile33_node42_cert).mp (by decide +kernel))

def profile33_node43_cert : CutBound 7 := { lost := (rows 32 32 33 16 0 0 0), upper := (rows 19 7 84 105 113 97 64), lower := (rows 19 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 70 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 107 111 68 72 64 96 64) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile33_node43 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,80] 6 97 profile33_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,80] 6 97 profile33_node43_cert).mp (by decide +kernel))

def profile33_node45_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 19 7 100 25 112 96 64), lower := (rows 19 7 100 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 11 127 8 0 127 127), good := (rows 103 103 100 111 100 100 100) }] }

theorem profile33_node45 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,17] 6 96 profile33_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,17] 6 96 profile33_node45_cert).mp (by decide +kernel))

def profile33_node46_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 19 7 100 41 80 112 64), lower := (rows 19 7 100 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 10 44 8 0 32 127), good := (rows 67 71 100 111 64 100 64) }] }

theorem profile33_node46 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,33] 6 80 profile33_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,33] 6 80 profile33_node46_cert).mp (by decide +kernel))

def profile33_node47_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 19 7 100 56 81 97 64), lower := (rows 19 7 100 56 16 32 64), losses := [{ target := 0, region := (rows 0 2 44 8 16 32 127), good := (rows 82 70 100 124 80 100 64) },{ target := 4, region := (rows 1 3 47 8 0 35 127), good := (rows 103 103 100 108 64 100 64) }] }

theorem profile33_node47 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,48] 6 65 profile33_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,48] 6 65 profile33_node47_cert).mp (by decide +kernel))

def profile33_node48_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 19 7 100 73 48 48 64), lower := (rows 19 7 100 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 36 11 0 32 127), good := (rows 75 79 100 73 64 100 64) }] }

theorem profile33_node48 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,65] 6 48 profile33_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,65] 6 48 profile33_node48_cert).mp (by decide +kernel))

def profile33_node49_cert : CutBound 7 := { lost := (rows 0 16 17 1 0 0 0), upper := (rows 19 7 100 88 49 33 64), lower := (rows 19 7 100 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 25 16 32 127), good := (rows 90 78 100 88 88 100 64) },{ target := 4, region := (rows 1 3 39 8 0 35 127), good := (rows 103 103 100 72 64 100 64) }] }

theorem profile33_node49 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,80] 6 33 profile33_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,80] 6 33 profile33_node49_cert).mp (by decide +kernel))

def profile33_node50_cert : CutBound 7 := { lost := (rows 0 0 17 17 0 0 0), upper := (rows 19 7 100 104 17 49 64), lower := (rows 19 7 100 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 44 44 16 32 127), good := (rows 82 78 108 108 80 108 64) },{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 67 79 108 108 64 108 64) }] }

theorem profile33_node50 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,96] 6 17 profile33_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96,96] 6 17 profile33_node50_cert).mp (by decide +kernel))

def profile33_node44_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node44_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node44 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5,96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node44_route profile33_node44_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node45
  · exact profile33_node46
  · exact profile33_node47
  · exact profile33_node48
  · exact profile33_node49
  · exact profile33_node50

def profile33_node38_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node38_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node38 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,5] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node38_route profile33_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node39
  · exact profile33_node40
  · exact profile33_node41
  · exact profile33_node42
  · exact profile33_node43
  · exact profile33_node44

def profile33_node51_cert : CutBound 7 := { lost := (rows 32 32 16 16 0 0 0), upper := (rows 19 19 101 109 117 101 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile33_node51 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,17] 6 101 profile33_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,17] 6 101 profile33_node51_cert).mp (by decide +kernel))

def profile33_node52_cert : CutBound 7 := { lost := (rows 32 0 16 16 0 0 0), upper := (rows 19 22 101 105 113 97 64), lower := (rows 19 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 70 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 87 68 72 80 64 64) }] }

theorem profile33_node52 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,20] 6 97 profile33_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,20] 6 97 profile33_node52_cert).mp (by decide +kernel))

def profile33_node54_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 19 35 21 108 116 100 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) },{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 67 99 111 72 64 96 64) }] }

theorem profile33_node54 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,17] 6 100 profile33_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,17] 6 100 profile33_node54_cert).mp (by decide +kernel))

def profile33_node55_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 19 35 37 92 84 116 64), lower := (rows 19 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) },{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 71 103 103 72 64 96 64) }] }

theorem profile33_node55 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,33] 6 84 profile33_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,33] 6 84 profile33_node55_cert).mp (by decide +kernel))

def profile33_node57_cert : CutBound 7 := { lost := (rows 32 16 1 0 0 0 0), upper := (rows 19 35 52 13 80 96 64), lower := (rows 19 35 52 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 11 4 8 0 127 127), good := (rows 99 99 100 111 96 96 96) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 83 84 93 80 80 80) }] }

theorem profile33_node57 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,5] 6 64 profile33_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,5] 6 64 profile33_node57_cert).mp (by decide +kernel))

def profile33_node58_cert : Bound 7 := { allowed := (rows 96 80 64 32 0 0 0), upper := (rows 19 35 52 73 84 100 64), lower := (rows 19 35 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 4 11 0 36 127), good := (rows 75 107 100 73 64 96 64) }] }

theorem profile33_node58 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,65] 6 68 profile33_node58_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,65] 6 68 profile33_node58_cert).mp (by decide +kernel))

def profile33_node59_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 19 35 52 76 81 97 64), lower := (rows 19 35 52 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 82 98 124 76 80 96 64) },{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 108 76 64 96 64) }] }

theorem profile33_node59 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,68] 6 65 profile33_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48,68] 6 65 profile33_node59_cert).mp (by decide +kernel))

def profile33_node56_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile33_node56_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node56 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,48] 6 (by decide) (choices 2) [5,65,68] profile33_node56_route profile33_node56_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node57
  · exact profile33_node58
  · exact profile33_node59

def profile33_node60_cert : CutBound 7 := { lost := (rows 0 0 48 1 0 0 0), upper := (rows 19 35 69 124 116 116 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 82 98 124 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 1 2 7 8 16 0 127), good := (rows 87 71 69 72 80 64 64) }] }

theorem profile33_node60 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,65] 6 116 profile33_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,65] 6 116 profile33_node60_cert).mp (by decide +kernel))

def profile33_node62_cert : CutBound 7 := { lost := (rows 0 16 33 32 0 0 0), upper := (rows 19 35 84 13 112 96 64), lower := (rows 19 35 84 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 11 4 8 0 127 127), good := (rows 99 99 100 111 96 96 96) },{ target := 5, region := (rows 1 2 21 11 16 0 127), good := (rows 95 79 84 77 84 64 64) }] }

theorem profile33_node62 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,5] 6 96 profile33_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,5] 6 96 profile33_node62_cert).mp (by decide +kernel))

def profile33_node63_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 19 35 84 41 84 100 64), lower := (rows 19 35 84 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 10 4 10 0 36 127), good := (rows 75 107 100 107 64 96 64) }] }

theorem profile33_node63 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,33] 6 68 profile33_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,33] 6 68 profile33_node63_cert).mp (by decide +kernel))

def profile33_node64_cert : CutBound 7 := { lost := (rows 0 16 1 1 0 0 0), upper := (rows 19 35 84 44 81 97 64), lower := (rows 19 35 84 44 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 10 16 32 127), good := (rows 94 110 84 108 84 96 64) },{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 68 108 64 96 64) }] }

theorem profile33_node64 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,36] 6 65 profile33_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,36] 6 65 profile33_node64_cert).mp (by decide +kernel))

def profile33_node65_cert : Bound 7 := { allowed := (rows 96 80 32 32 0 0 0), upper := (rows 19 35 84 73 52 36 64), lower := (rows 19 35 84 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 4 11 0 36 127), good := (rows 75 107 100 73 64 96 64) }] }

theorem profile33_node65 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,65] 6 36 profile33_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,65] 6 36 profile33_node65_cert).mp (by decide +kernel))

def profile33_node66_cert : CutBound 7 := { lost := (rows 0 16 1 17 0 0 0), upper := (rows 19 35 84 76 49 33 64), lower := (rows 19 35 84 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 31 16 32 127), good := (rows 94 110 92 76 92 96 64) },{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 76 76 64 96 64) }] }

theorem profile33_node66 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,68] 6 33 profile33_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,68] 6 33 profile33_node66_cert).mp (by decide +kernel))

def profile33_node67_cert : Bound 7 := { allowed := (rows 96 80 32 16 0 0 0), upper := (rows 19 35 84 104 21 37 64), lower := (rows 19 35 84 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 42 16 32 127), good := (rows 94 110 84 104 84 104 64) }] }

theorem profile33_node67 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,96] 6 5 profile33_node67_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80,96] 6 5 profile33_node67_cert).mp (by decide +kernel))

def profile33_node61_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node61_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node61 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,80] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile33_node61_route profile33_node61_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node62
  · exact profile33_node63
  · exact profile33_node64
  · exact profile33_node65
  · exact profile33_node66
  · exact profile33_node67

def profile33_node69_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 19 35 100 13 80 112 64), lower := (rows 19 35 100 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 38 11 0 32 127), good := (rows 79 111 100 77 64 100 64) }] }

theorem profile33_node69 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,5] 6 80 profile33_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,5] 6 80 profile33_node69_cert).mp (by decide +kernel))

def profile33_node70_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 19 35 100 25 84 100 64), lower := (rows 19 35 100 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 11 127 8 0 127 127), good := (rows 103 103 100 111 100 100 100) }] }

theorem profile33_node70 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,17] 6 68 profile33_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,17] 6 68 profile33_node70_cert).mp (by decide +kernel))

def profile33_node71_cert : CutBound 7 := { lost := (rows 0 16 17 1 0 0 0), upper := (rows 19 35 100 28 81 97 64), lower := (rows 19 35 100 28 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 9 16 32 127), good := (rows 94 110 100 92 80 100 64) },{ target := 4, region := (rows 1 3 39 8 0 35 127), good := (rows 103 103 100 76 64 100 64) }] }

theorem profile33_node71 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,20] 6 65 profile33_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,20] 6 65 profile33_node71_cert).mp (by decide +kernel))

def profile33_node72_cert : CutBound 7 := { lost := (rows 0 0 17 16 0 0 0), upper := (rows 19 35 100 73 20 52 64), lower := (rows 19 35 100 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 124 116 116 116) },{ target := 4, region := (rows 1 2 38 11 0 32 127), good := (rows 79 111 100 73 64 100 64) }] }

theorem profile33_node72 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,65] 6 20 profile33_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,65] 6 20 profile33_node72_cert).mp (by decide +kernel))

def profile33_node73_cert : CutBound 7 := { lost := (rows 0 0 17 17 0 0 0), upper := (rows 19 35 100 76 17 49 64), lower := (rows 19 35 100 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 47 16 32 127), good := (rows 94 110 108 76 80 108 64) },{ target := 4, region := (rows 1 2 38 47 0 32 127), good := (rows 79 111 108 76 64 108 64) }] }

theorem profile33_node73 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,68] 6 17 profile33_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,68] 6 17 profile33_node73_cert).mp (by decide +kernel))

def profile33_node74_cert : Bound 7 := { allowed := (rows 96 80 16 32 0 0 0), upper := (rows 19 35 100 88 21 37 64), lower := (rows 19 35 100 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 25 16 32 127), good := (rows 94 110 100 88 88 100 64) }] }

theorem profile33_node74 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,80] 6 5 profile33_node74_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96,80] 6 5 profile33_node74_cert).mp (by decide +kernel))

def profile33_node68_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile33_node68_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node68 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33,96] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile33_node68_route profile33_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node69
  · exact profile33_node70
  · exact profile33_node71
  · exact profile33_node72
  · exact profile33_node73
  · exact profile33_node74

def profile33_node53_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node53_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node53 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,33] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node53_route profile33_node53_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node54
  · exact profile33_node55
  · exact profile33_node56
  · exact profile33_node60
  · exact profile33_node61
  · exact profile33_node68

def profile33_node76_cert : CutBound 7 := { lost := (rows 0 16 32 16 0 0 0), upper := (rows 19 38 21 105 113 97 64), lower := (rows 19 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 13 0 37 127), good := (rows 107 110 111 72 64 96 64) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 87 70 85 72 80 64 64) }] }

theorem profile33_node76 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,17] 6 97 profile33_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,17] 6 97 profile33_node76_cert).mp (by decide +kernel))

def profile33_node77_cert : CutBound 7 := { lost := (rows 32 17 0 32 0 0 0), upper := (rows 19 38 37 89 81 113 64), lower := (rows 19 38 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 102 102 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 102 103 72 64 96 64) },{ target := 5, region := (rows 3 2 4 15 23 0 127), good := (rows 91 95 93 72 80 64 64) }] }

theorem profile33_node77 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,33] 6 81 profile33_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,33] 6 81 profile33_node77_cert).mp (by decide +kernel))

def profile33_node78_cert : CutBound 7 := { lost := (rows 0 17 0 16 0 0 0), upper := (rows 19 38 52 73 81 97 64), lower := (rows 19 38 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 102 118 72 80 96 64) },{ target := 4, region := (rows 1 6 4 9 0 33 127), good := (rows 107 102 102 72 64 96 64) }] }

theorem profile33_node78 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,48] 6 65 profile33_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,48] 6 65 profile33_node78_cert).mp (by decide +kernel))

def profile33_node80_cert : CutBound 7 := { lost := (rows 0 17 16 0 0 0 0), upper := (rows 19 38 69 25 112 96 64), lower := (rows 19 38 69 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 1 15 13 8 0 127 127), good := (rows 103 102 103 111 96 96 96) }] }

theorem profile33_node80 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,17] 6 96 profile33_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,17] 6 96 profile33_node80_cert).mp (by decide +kernel))

def profile33_node81_cert : CutBound 7 := { lost := (rows 0 17 16 0 0 0 0), upper := (rows 19 38 69 41 80 112 64), lower := (rows 19 38 69 41 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 1 10 13 8 0 32 127), good := (rows 71 102 69 111 64 96 64) }] }

theorem profile33_node81 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,33] 6 80 profile33_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,33] 6 80 profile33_node81_cert).mp (by decide +kernel))

def profile33_node82_cert : CutBound 7 := { lost := (rows 32 16 48 0 0 0 0), upper := (rows 19 38 69 56 81 97 64), lower := (rows 19 38 69 56 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 8 0 37 127), good := (rows 103 102 103 104 64 96 64) },{ target := 5, region := (rows 3 2 7 8 23 0 127), good := (rows 87 87 85 88 80 64 64) }] }

theorem profile33_node82 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,48] 6 65 profile33_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,48] 6 65 profile33_node82_cert).mp (by decide +kernel))

def profile33_node83_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 19 38 69 73 48 48 64), lower := (rows 19 38 69 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 1 2 13 13 0 32 127), good := (rows 79 110 77 77 64 96 64) }] }

theorem profile33_node83 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,65] 6 48 profile33_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,65] 6 48 profile33_node83_cert).mp (by decide +kernel))

def profile33_node84_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 19 38 69 88 49 33 64), lower := (rows 19 38 69 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 90 102 76 88 88 96 64) },{ target := 4, region := (rows 1 7 5 8 0 37 127), good := (rows 103 102 103 72 64 96 64) }] }

theorem profile33_node84 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,80] 6 33 profile33_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,80] 6 33 profile33_node84_cert).mp (by decide +kernel))

def profile33_node85_cert : CutBound 7 := { lost := (rows 0 0 16 17 0 0 0), upper := (rows 19 38 69 104 17 49 64), lower := (rows 19 38 69 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 127), good := (rows 90 110 68 104 80 104 64) },{ target := 4, region := (rows 1 2 5 42 0 32 127), good := (rows 79 110 69 104 64 104 64) }] }

theorem profile33_node85 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,96] 6 17 profile33_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65,96] 6 17 profile33_node85_cert).mp (by decide +kernel))

def profile33_node79_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node79_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node79 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,65] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node79_route profile33_node79_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node80
  · exact profile33_node81
  · exact profile33_node82
  · exact profile33_node83
  · exact profile33_node84
  · exact profile33_node85

def profile33_node86_cert : CutBound 7 := { lost := (rows 0 0 33 16 0 0 0), upper := (rows 19 38 84 105 113 97 64), lower := (rows 19 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 107 102 68 72 64 96 64) },{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 70 84 72 84 64 64) }] }

theorem profile33_node86 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,80] 6 97 profile33_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,80] 6 97 profile33_node86_cert).mp (by decide +kernel))

def profile33_node87_cert : CutBound 7 := { lost := (rows 0 17 17 0 0 0 0), upper := (rows 19 38 100 89 81 113 64), lower := (rows 19 38 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 86 102 102 72 80 102 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile33_node87 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,96] 6 81 profile33_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36,96] 6 81 profile33_node87_cert).mp (by decide +kernel))

def profile33_node75_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node75_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node75 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,36] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node75_route profile33_node75_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node76
  · exact profile33_node77
  · exact profile33_node78
  · exact profile33_node79
  · exact profile33_node86
  · exact profile33_node87

def profile33_node88_cert : CutBound 7 := { lost := (rows 32 0 16 16 0 0 0), upper := (rows 19 50 101 109 117 101 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile33_node88 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,48] 6 101 profile33_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,48] 6 101 profile33_node88_cert).mp (by decide +kernel))

def profile33_node89_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 19 67 117 125 117 117 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile33_node89 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,65] 6 117 profile33_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,65] 6 117 profile33_node89_cert).mp (by decide +kernel))

def profile33_node90_cert : CutBound 7 := { lost := (rows 0 49 0 0 0 0 0), upper := (rows 19 70 117 121 113 113 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 82 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 70 70 72 64 96 64) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 83 70 70 72 80 64 64) }] }

theorem profile33_node90 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,68] 6 113 profile33_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,68] 6 113 profile33_node90_cert).mp (by decide +kernel))

def profile33_node91_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 19 82 101 109 117 101 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 66 68 72 64 96 64) }] }

theorem profile33_node91 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,80] 6 101 profile33_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,80] 6 101 profile33_node91_cert).mp (by decide +kernel))

def profile33_node93_cert : CutBound 7 := { lost := (rows 0 17 0 16 0 0 0), upper := (rows 19 98 21 109 117 101 64), lower := (rows 19 98 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 84 72 80 98 64) },{ target := 4, region := (rows 1 38 4 12 0 36 127), good := (rows 67 98 111 72 64 98 64) }] }

theorem profile33_node93 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,17] 6 101 profile33_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,17] 6 101 profile33_node93_cert).mp (by decide +kernel))

def profile33_node94_cert : CutBound 7 := { lost := (rows 0 17 0 32 0 0 0), upper := (rows 19 98 37 93 85 117 64), lower := (rows 19 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 8 16 32 127), good := (rows 82 98 102 72 80 98 64) },{ target := 4, region := (rows 1 38 4 8 0 32 127), good := (rows 67 98 103 72 64 98 64) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 83 66 93 72 80 64 64) }] }

theorem profile33_node94 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,33] 6 85 profile33_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,33] 6 85 profile33_node94_cert).mp (by decide +kernel))

def profile33_node96_cert : CutBound 7 := { lost := (rows 32 17 0 0 0 0 0), upper := (rows 19 98 52 13 81 97 64), lower := (rows 19 98 52 13 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 8 16 32 127), good := (rows 82 98 118 78 80 98 64) },{ target := 4, region := (rows 1 47 4 8 0 41 127), good := (rows 99 98 102 111 64 98 64) },{ target := 5, region := (rows 3 2 4 8 27 0 127), good := (rows 83 83 84 93 80 64 64) }] }

theorem profile33_node96 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,5] 6 65 profile33_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,5] 6 65 profile33_node96_cert).mp (by decide +kernel))

def profile33_node97_cert : CutBound 7 := { lost := (rows 0 17 0 16 0 0 0), upper := (rows 19 98 52 73 21 37 64), lower := (rows 19 98 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 8 16 32 127), good := (rows 82 98 118 72 80 98 64) },{ target := 4, region := (rows 1 38 4 9 0 32 127), good := (rows 75 98 102 73 64 98 64) }] }

theorem profile33_node97 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,65] 6 5 profile33_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,65] 6 5 profile33_node97_cert).mp (by decide +kernel))

def profile33_node98_cert : CutBound 7 := { lost := (rows 0 17 0 17 0 0 0), upper := (rows 19 98 52 76 17 33 64), lower := (rows 19 98 52 76 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 12 16 32 127), good := (rows 82 98 126 78 80 98 64) },{ target := 4, region := (rows 1 39 4 12 0 33 127), good := (rows 99 98 110 78 64 98 64) }] }

theorem profile33_node98 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,68] 6 1 profile33_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48,68] 6 1 profile33_node98_cert).mp (by decide +kernel))

def profile33_node95_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile33_node95_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node95 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,48] 6 (by decide) (choices 2) [5,65,68] profile33_node95_route profile33_node95_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node96
  · exact profile33_node97
  · exact profile33_node98

def profile33_node99_cert : CutBound 7 := { lost := (rows 0 17 16 0 0 0 0), upper := (rows 19 98 69 61 53 53 64), lower := (rows 19 98 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 5 8 0 32 127), good := (rows 71 98 69 72 64 98 64) }] }

theorem profile33_node99 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,65] 6 53 profile33_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,65] 6 53 profile33_node99_cert).mp (by decide +kernel))

def profile33_node100_cert : CutBound 7 := { lost := (rows 0 17 1 0 0 0 0), upper := (rows 19 98 84 45 53 37 64), lower := (rows 19 98 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 21 8 16 32 127), good := (rows 86 98 84 72 84 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile33_node100 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,80] 6 37 profile33_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,80] 6 37 profile33_node100_cert).mp (by decide +kernel))

def profile33_node101_cert : CutBound 7 := { lost := (rows 0 17 17 0 0 0 0), upper := (rows 19 98 100 29 21 53 64), lower := (rows 19 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 86 102 102 72 80 102 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile33_node101 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,96] 6 21 profile33_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96,96] 6 21 profile33_node101_cert).mp (by decide +kernel))

def profile33_node92_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node92_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node92 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18,96] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node92_route profile33_node92_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node93
  · exact profile33_node94
  · exact profile33_node95
  · exact profile33_node99
  · exact profile33_node100
  · exact profile33_node101

def profile33_node37_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node37_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node37 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [18] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile33_node37_route profile33_node37_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node38
  · exact profile33_node51
  · exact profile33_node52
  · exact profile33_node53
  · exact profile33_node75
  · exact profile33_node88
  · exact profile33_node89
  · exact profile33_node90
  · exact profile33_node91
  · exact profile33_node92

def profile33_node104_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 7 7 120 112 112 64), lower := (rows 49 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile33_node104 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,3] 6 112 profile33_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,3] 6 112 profile33_node104_cert).mp (by decide +kernel))

def profile33_node105_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 49 7 21 106 114 98 64), lower := (rows 49 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 84 72 80 96 64) },{ target := 4, region := (rows 1 6 4 14 0 38 127), good := (rows 97 111 111 72 64 96 64) }] }

theorem profile33_node105 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,17] 6 98 profile33_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,17] 6 98 profile33_node105_cert).mp (by decide +kernel))

def profile33_node106_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 7 22 105 113 97 64), lower := (rows 49 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 105 111 110 72 64 96 64) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile33_node106 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,18] 6 97 profile33_node106_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,18] 6 97 profile33_node106_cert).mp (by decide +kernel))

def profile33_node107_cert : CutBound 7 := { lost := (rows 0 0 1 48 0 0 0), upper := (rows 49 7 52 75 83 99 64), lower := (rows 49 7 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 116 70 116 72 80 96 64) },{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 100 72 64 96 64) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 81 95 84 72 80 64 64) }] }

theorem profile33_node107 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,48] 6 67 profile33_node107_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,48] 6 67 profile33_node107_cert).mp (by decide +kernel))

def profile33_node108_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 7 69 122 114 114 64), lower := (rows 49 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 68 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile33_node108 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,65] 6 114 profile33_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,65] 6 114 profile33_node108_cert).mp (by decide +kernel))

def profile33_node109_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 49 7 70 121 113 113 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile33_node109 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,66] 6 113 profile33_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,66] 6 113 profile33_node109_cert).mp (by decide +kernel))

def profile33_node110_cert : CutBound 7 := { lost := (rows 0 32 33 16 0 0 0), upper := (rows 49 7 84 107 115 99 64), lower := (rows 49 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 68 72 64 96 64) },{ target := 5, region := (rows 1 3 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile33_node110 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,80] 6 99 profile33_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5,80] 6 99 profile33_node110_cert).mp (by decide +kernel))

def profile33_node103_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node103_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node103 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,5] 6 (by decide) (choices 2) [3,17,18,48,65,66,80] profile33_node103_route profile33_node103_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node104
  · exact profile33_node105
  · exact profile33_node106
  · exact profile33_node107
  · exact profile33_node108
  · exact profile33_node109
  · exact profile33_node110

def profile33_node111_cert : CutBound 7 := { lost := (rows 0 32 16 16 0 0 0), upper := (rows 49 19 103 111 119 103 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile33_node111 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,17] 6 103 profile33_node111_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,17] 6 103 profile33_node111_cert).mp (by decide +kernel))

def profile33_node113_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 22 7 105 113 97 64), lower := (rows 49 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 105 110 111 72 64 96 64) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 86 71 72 80 64 64) }] }

theorem profile33_node113 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,3] 6 97 profile33_node113_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,3] 6 97 profile33_node113_cert).mp (by decide +kernel))

def profile33_node114_cert : CutBound 7 := { lost := (rows 0 32 16 32 0 0 0), upper := (rows 49 22 37 75 83 99 64), lower := (rows 49 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 101 72 64 96 64) },{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 81 94 95 72 80 64 64) }] }

theorem profile33_node114 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,33] 6 67 profile33_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,33] 6 67 profile33_node114_cert).mp (by decide +kernel))

def profile33_node115_cert : CutBound 7 := { lost := (rows 0 1 1 16 0 0 0), upper := (rows 49 22 38 73 81 97 64), lower := (rows 49 22 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 5 8 16 32 127), good := (rows 118 86 102 72 80 96 64) },{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 102 72 64 96 64) }] }

theorem profile33_node115 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,34] 6 65 profile33_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,34] 6 65 profile33_node115_cert).mp (by decide +kernel))

def profile33_node116_cert : CutBound 7 := { lost := (rows 0 32 48 0 0 0 0), upper := (rows 49 22 69 107 115 99 64), lower := (rows 49 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 69 72 64 96 64) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 86 71 72 80 64 64) }] }

theorem profile33_node116 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,65] 6 99 profile33_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,65] 6 99 profile33_node116_cert).mp (by decide +kernel))

def profile33_node117_cert : CutBound 7 := { lost := (rows 0 1 17 16 0 0 0), upper := (rows 49 22 70 105 113 97 64), lower := (rows 49 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) },{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 70 70 72 64 96 64) }] }

theorem profile33_node117 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,66] 6 97 profile33_node117_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,66] 6 97 profile33_node117_cert).mp (by decide +kernel))

def profile33_node118_cert : CutBound 7 := { lost := (rows 0 1 17 0 0 0 0), upper := (rows 49 22 100 75 83 99 64), lower := (rows 49 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 37 8 16 32 127), good := (rows 118 86 100 72 80 100 64) },{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 101 70 100 72 64 100 64) }] }

theorem profile33_node118 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,96] 6 67 profile33_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20,96] 6 67 profile33_node118_cert).mp (by decide +kernel))

def profile33_node112_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node112_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node112 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,20] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile33_node112_route profile33_node112_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node113
  · exact profile33_node114
  · exact profile33_node115
  · exact profile33_node116
  · exact profile33_node117
  · exact profile33_node118

def profile33_node119_cert : CutBound 7 := { lost := (rows 64 65 0 0 0 0 0), upper := (rows 49 50 71 79 87 103 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 114 114 68 72 80 96 64) },{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile33_node119 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,48] 6 71 profile33_node119_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,48] 6 71 profile33_node119_cert).mp (by decide +kernel))

def profile33_node121_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 67 7 124 116 116 64), lower := (rows 49 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 112 66 126 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile33_node121 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,3] 6 116 profile33_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,3] 6 116 profile33_node121_cert).mp (by decide +kernel))

def profile33_node122_cert : CutBound 7 := { lost := (rows 0 48 32 16 0 0 0), upper := (rows 49 67 21 110 118 102 64), lower := (rows 49 67 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 7 4 12 0 36 127), good := (rows 99 67 111 72 64 96 64) },{ target := 5, region := (rows 1 7 5 8 16 0 127), good := (rows 87 71 87 72 80 64 64) }] }

theorem profile33_node122 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,17] 6 102 profile33_node122_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,17] 6 102 profile33_node122_cert).mp (by decide +kernel))

def profile33_node123_cert : CutBound 7 := { lost := (rows 0 48 32 0 0 0 0), upper := (rows 49 67 22 109 117 101 64), lower := (rows 49 67 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 70 72 64 96 64) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile33_node123 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,18] 6 101 profile33_node123_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,18] 6 101 profile33_node123_cert).mp (by decide +kernel))

def profile33_node124_cert : CutBound 7 := { lost := (rows 0 48 1 0 0 0 0), upper := (rows 49 67 52 79 87 103 64), lower := (rows 49 67 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 116 70 116 72 80 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 100 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 84 72 80 64 64) }] }

theorem profile33_node124 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,48] 6 71 profile33_node124_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,48] 6 71 profile33_node124_cert).mp (by decide +kernel))

def profile33_node125_cert : CutBound 7 := { lost := (rows 0 48 48 0 0 0 0), upper := (rows 49 67 69 62 54 54 64), lower := (rows 49 67 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 87 71 71 72 80 64 64) }] }

theorem profile33_node125 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,65] 6 54 profile33_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,65] 6 54 profile33_node125_cert).mp (by decide +kernel))

def profile33_node126_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 49 67 70 61 53 53 64), lower := (rows 49 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile33_node126 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,66] 6 53 profile33_node126_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,66] 6 53 profile33_node126_cert).mp (by decide +kernel))

def profile33_node127_cert : CutBound 7 := { lost := (rows 0 48 33 0 0 0 0), upper := (rows 49 67 84 47 55 39 64), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) },{ target := 5, region := (rows 1 3 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile33_node127 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,80] 6 39 profile33_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65,80] 6 39 profile33_node127_cert).mp (by decide +kernel))

def profile33_node120_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node120_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node120 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,65] 6 (by decide) (choices 2) [3,17,18,48,65,66,80] profile33_node120_route profile33_node120_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node121
  · exact profile33_node122
  · exact profile33_node123
  · exact profile33_node124
  · exact profile33_node125
  · exact profile33_node126
  · exact profile33_node127

def profile33_node128_cert : CutBound 7 := { lost := (rows 0 49 0 0 0 0 0), upper := (rows 49 70 119 123 115 115 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 97 70 70 72 64 96 64) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 81 70 70 72 80 64 64) }] }

theorem profile33_node128 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,68] 6 115 profile33_node128_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,68] 6 115 profile33_node128_cert).mp (by decide +kernel))

def profile33_node130_cert : CutBound 7 := { lost := (rows 0 33 32 16 0 0 0), upper := (rows 49 82 7 109 117 101 64), lower := (rows 49 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 97 66 111 72 64 96 64) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile33_node130 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,3] 6 101 profile33_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,3] 6 101 profile33_node130_cert).mp (by decide +kernel))


#print axioms profile33_node130
end Delivery.SmallBudgetTenFinite7
