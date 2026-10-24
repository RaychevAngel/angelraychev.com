import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile9_node2_cert : CutBound 7 := { lost := (rows 0 32 16 16 0 0 0), upper := (rows 51 19 103 107 115 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile9_node2 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,17] 6 99 profile9_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,17] 6 99 profile9_node2_cert).mp (by decide +kernel))

def profile9_node3_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 51 35 87 91 83 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile9_node3 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,33] 6 83 profile9_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,33] 6 83 profile9_node3_cert).mp (by decide +kernel))

def profile9_node4_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 51 50 71 75 83 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile9_node4 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,48] 6 67 profile9_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,48] 6 67 profile9_node4_cert).mp (by decide +kernel))

def profile9_node6_cert : CutBound 7 := { lost := (rows 0 16 16 3 0 0 0), upper := (rows 51 67 7 120 112 32 64), lower := (rows 51 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 121 125 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile9_node6 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,3] 6 112 profile9_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,3] 6 112 profile9_node6_cert).mp (by decide +kernel))

def profile9_node7_cert : CutBound 7 := { lost := (rows 0 16 2 17 0 0 0), upper := (rows 51 67 21 106 114 32 64), lower := (rows 51 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 5 8 16 127 127), good := (rows 117 101 117 104 112 96 96) },{ target := 4, region := (rows 1 7 4 15 0 127 127), good := (rows 107 107 111 104 96 96 96) }] }

theorem profile9_node7 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,17] 6 98 profile9_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,17] 6 98 profile9_node7_cert).mp (by decide +kernel))

def profile9_node8_cert : CutBound 7 := { lost := (rows 0 16 1 18 0 0 0), upper := (rows 51 67 22 105 113 32 64), lower := (rows 51 67 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 127 127), good := (rows 118 102 118 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 121 124 104 112 96 96) },{ target := 4, region := (rows 1 3 4 11 0 127 127), good := (rows 107 107 110 104 96 96 96) }] }

theorem profile9_node8 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,18] 6 97 profile9_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,18] 6 97 profile9_node8_cert).mp (by decide +kernel))

def profile9_node9_cert : CutBound 7 := { lost := (rows 0 16 18 1 0 0 0), upper := (rows 51 67 37 90 82 32 64), lower := (rows 51 67 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 117 101 101 104 112 96 96) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile9_node9 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,33] 6 82 profile9_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,33] 6 82 profile9_node9_cert).mp (by decide +kernel))

def profile9_node10_cert : CutBound 7 := { lost := (rows 0 16 17 2 0 0 0), upper := (rows 51 67 38 89 81 32 64), lower := (rows 51 67 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 118 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 121 124 104 112 96 96) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile9_node10 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,34] 6 81 profile9_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,34] 6 81 profile9_node10_cert).mp (by decide +kernel))

def profile9_node11_cert : CutBound 7 := { lost := (rows 0 16 3 16 0 0 0), upper := (rows 51 67 52 75 83 32 64), lower := (rows 51 67 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 127 127), good := (rows 118 102 116 104 116 96 96) },{ target := 1, region := (rows 1 0 21 8 16 127 127), good := (rows 117 101 116 104 116 96 96) },{ target := 4, region := (rows 1 3 4 11 0 127 127), good := (rows 107 107 100 104 96 96 96) }] }

theorem profile9_node11 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,48] 6 67 profile9_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,48] 6 67 profile9_node11_cert).mp (by decide +kernel))

def profile9_node12_cert : CutBound 7 := { lost := (rows 0 16 18 1 0 0 0), upper := (rows 51 67 69 58 50 32 64), lower := (rows 51 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 117 101 101 104 112 96 96) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile9_node12 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,65] 6 50 profile9_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,65] 6 50 profile9_node12_cert).mp (by decide +kernel))

def profile9_node13_cert : CutBound 7 := { lost := (rows 0 16 17 2 0 0 0), upper := (rows 51 67 70 57 49 32 64), lower := (rows 51 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 118 102 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 121 124 104 112 96 96) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile9_node13 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,66] 6 49 profile9_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,66] 6 49 profile9_node13_cert).mp (by decide +kernel))

def profile9_node14_cert : CutBound 7 := { lost := (rows 0 16 3 16 0 0 0), upper := (rows 51 67 84 43 51 32 64), lower := (rows 51 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 127 127), good := (rows 118 102 116 104 116 96 96) },{ target := 1, region := (rows 1 0 21 8 16 127 127), good := (rows 117 101 116 104 116 96 96) },{ target := 4, region := (rows 1 3 4 11 0 127 127), good := (rows 107 107 100 104 96 96 96) }] }

theorem profile9_node14 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,80] 6 35 profile9_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,80] 6 35 profile9_node14_cert).mp (by decide +kernel))

def profile9_node15_cert : CutBound 7 := { lost := (rows 0 16 19 0 0 0 0), upper := (rows 51 67 100 27 19 32 64), lower := (rows 51 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 118 102 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 117 101 100 108 116 100 100) },{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile9_node15 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,96] 6 19 profile9_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65,96] 6 19 profile9_node15_cert).mp (by decide +kernel))

def profile9_node5_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile9_node5_route : Route 7 := (fun mask => (mask,id))

theorem profile9_node5 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,65] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile9_node5_route profile9_node5_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node6
  · exact profile9_node7
  · exact profile9_node8
  · exact profile9_node9
  · exact profile9_node10
  · exact profile9_node11
  · exact profile9_node12
  · exact profile9_node13
  · exact profile9_node14
  · exact profile9_node15

def profile9_node16_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 51 82 103 107 115 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile9_node16 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,80] 6 99 profile9_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,80] 6 99 profile9_node16_cert).mp (by decide +kernel))

def profile9_node17_cert : CutBound 7 := { lost := (rows 0 17 32 32 0 0 0), upper := (rows 51 98 87 91 83 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile9_node17 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,96] 6 83 profile9_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50,96] 6 83 profile9_node17_cert).mp (by decide +kernel))

def profile9_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile9_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [50] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile9_node1_route profile9_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node2
  · exact profile9_node3
  · exact profile9_node4
  · exact profile9_node5
  · exact profile9_node16
  · exact profile9_node17

def profile9_node20_cert : CutBound 7 := { lost := (rows 16 0 16 3 0 0 0), upper := (rows 99 19 7 120 112 32 64), lower := (rows 99 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 121 125 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile9_node20 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,3] 6 112 profile9_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,3] 6 112 profile9_node20_cert).mp (by decide +kernel))

def profile9_node21_cert : CutBound 7 := { lost := (rows 16 0 2 17 0 0 0), upper := (rows 99 19 21 106 114 32 64), lower := (rows 99 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 6 8 16 127 127), good := (rows 101 117 117 104 112 96 96) },{ target := 4, region := (rows 3 2 4 11 0 127 127), good := (rows 107 107 109 104 96 96 96) }] }

theorem profile9_node21 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,17] 6 98 profile9_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,17] 6 98 profile9_node21_cert).mp (by decide +kernel))

def profile9_node22_cert : CutBound 7 := { lost := (rows 16 0 1 18 0 0 0), upper := (rows 99 19 22 105 113 32 64), lower := (rows 99 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 102 118 118 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 121 124 104 112 96 96) },{ target := 4, region := (rows 7 2 4 15 0 127 127), good := (rows 107 107 111 104 96 96 96) }] }

theorem profile9_node22 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,18] 6 97 profile9_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,18] 6 97 profile9_node22_cert).mp (by decide +kernel))

def profile9_node23_cert : CutBound 7 := { lost := (rows 16 0 18 1 0 0 0), upper := (rows 99 19 37 90 82 32 64), lower := (rows 99 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 127 127), good := (rows 122 122 124 104 112 96 96) },{ target := 1, region := (rows 1 0 7 8 16 127 127), good := (rows 101 117 101 104 112 96 96) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile9_node23 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,33] 6 82 profile9_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,33] 6 82 profile9_node23_cert).mp (by decide +kernel))

def profile9_node24_cert : CutBound 7 := { lost := (rows 16 0 17 2 0 0 0), upper := (rows 99 19 38 89 81 32 64), lower := (rows 99 19 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 127 127), good := (rows 102 118 102 104 112 96 96) },{ target := 1, region := (rows 1 0 4 11 19 127 127), good := (rows 121 121 124 104 112 96 96) },{ target := 4, region := (rows 7 2 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile9_node24 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,34] 6 81 profile9_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,34] 6 81 profile9_node24_cert).mp (by decide +kernel))

def profile9_node25_cert : CutBound 7 := { lost := (rows 16 0 3 16 0 0 0), upper := (rows 99 19 52 75 83 32 64), lower := (rows 99 19 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 127 127), good := (rows 102 118 116 104 116 96 96) },{ target := 1, region := (rows 1 0 22 8 16 127 127), good := (rows 101 117 116 104 116 96 96) },{ target := 4, region := (rows 3 2 4 11 0 127 127), good := (rows 107 107 100 104 96 96 96) }] }

theorem profile9_node25 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,48] 6 67 profile9_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,48] 6 67 profile9_node25_cert).mp (by decide +kernel))

def profile9_node26_cert : CutBound 7 := { lost := (rows 16 0 19 0 0 0 0), upper := (rows 99 19 100 27 19 32 64), lower := (rows 99 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 118 100 108 116 100 100) },{ target := 1, region := (rows 1 0 127 8 16 127 127), good := (rows 101 117 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile9_node26 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,96] 6 19 profile9_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17,96] 6 19 profile9_node26_cert).mp (by decide +kernel))

def profile9_node19_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile9_node19_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node19 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile9_node19_route profile9_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node20
  · exact profile9_node21
  · exact profile9_node22
  · exact profile9_node23
  · exact profile9_node24
  · exact profile9_node25
  · exact profile9_node26

def profile9_node27_cert : CutBound 7 := { lost := (rows 16 16 32 32 0 0 0), upper := (rows 99 35 87 91 83 32 64), lower := (rows 99 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) },{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile9_node27 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,33] 6 83 profile9_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,33] 6 83 profile9_node27_cert).mp (by decide +kernel))

def profile9_node28_cert : CutBound 7 := { lost := (rows 16 1 32 32 0 0 0), upper := (rows 99 50 87 91 83 32 64), lower := (rows 99 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 98 114 100 104 114 96 96) },{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile9_node28 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,48] 6 83 profile9_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,48] 6 83 profile9_node28_cert).mp (by decide +kernel))

def profile9_node29_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 99 98 23 27 19 32 64), lower := (rows 99 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) }] }

theorem profile9_node29 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,96] 6 19 profile9_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98,96] 6 19 profile9_node29_cert).mp (by decide +kernel))

def profile9_node18_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile9_node18_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node18 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [98] 6 (by decide) (choices 2) [17,33,48,96] profile9_node18_route profile9_node18_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node19
  · exact profile9_node27
  · exact profile9_node28
  · exact profile9_node29

def profile9_node31_cert : CutBound 7 := { lost := (rows 2 0 16 16 0 0 0), upper := (rows 113 19 103 107 115 32 64), lower := (rows 113 19 4 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 113 100 104 113 96 96) },{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile9_node31 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,17] 6 99 profile9_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,17] 6 99 profile9_node31_cert).mp (by decide +kernel))

def profile9_node32_cert : CutBound 7 := { lost := (rows 2 16 32 32 0 0 0), upper := (rows 113 35 87 91 83 32 64), lower := (rows 113 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 97 100 104 113 96 96) },{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 81 95 68 72 80 64 64) }] }

theorem profile9_node32 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,33] 6 83 profile9_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,33] 6 83 profile9_node32_cert).mp (by decide +kernel))

def profile9_node33_cert : CutBound 7 := { lost := (rows 2 65 0 0 0 0 0), upper := (rows 113 50 71 75 83 32 64), lower := (rows 113 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 1, region := (rows 19 0 4 8 16 127 127), good := (rows 113 113 100 104 113 96 96) },{ target := 6, region := (rows 1 19 4 8 16 127 0), good := (rows 51 50 36 40 50 32 32) }] }

theorem profile9_node33 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,48] 6 67 profile9_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,48] 6 67 profile9_node33_cert).mp (by decide +kernel))

def profile9_node34_cert : CutBound 7 := { lost := (rows 2 17 0 0 0 0 0), upper := (rows 113 98 23 27 19 32 64), lower := (rows 113 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) },{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 96 100 104 113 96 96) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile9_node34 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,96] 6 19 profile9_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112,96] 6 19 profile9_node34_cert).mp (by decide +kernel))

def profile9_node30_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile9_node30_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node30 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [112] 6 (by decide) (choices 2) [17,33,48,96] profile9_node30_route profile9_node30_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node31
  · exact profile9_node32
  · exact profile9_node33
  · exact profile9_node34

def profile9_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile9_node0_route : Route 7 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile9_node0 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [] 6 (by decide) (choices 3) [50,98,112] profile9_node0_route profile9_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node1
  · exact profile9_node18
  · exact profile9_node30

theorem profile9 : Upper (D (n:=7) [50,34,32,32,18,2,2]) (R (n:=7) [50,34,32,32,18,2,2]) [] 6 := profile9_node0


#print axioms profile9
end Delivery.SmallBudgetTenFinite7
