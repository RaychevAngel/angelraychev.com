import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile32_node2_cert : CutBound 7 := { lost := (rows 32 32 16 16 0 0 0), upper := (rows 19 19 103 107 115 99 64), lower := (rows 19 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 127), good := (rows 111 111 68 72 64 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile32_node2 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,17] 6 99 profile32_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,17] 6 99 profile32_node2_cert).mp (by decide +kernel))

def profile32_node4_cert : CutBound 7 := { lost := (rows 0 0 48 3 0 0 0), upper := (rows 19 35 7 120 112 112 64), lower := (rows 19 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 121 125 120 120 120 120) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) },{ target := 5, region := (rows 1 2 7 8 16 0 127), good := (rows 87 71 71 72 80 64 64) }] }

theorem profile32_node4 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,3] 6 112 profile32_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,3] 6 112 profile32_node4_cert).mp (by decide +kernel))

def profile32_node5_cert : CutBound 7 := { lost := (rows 0 16 2 17 0 0 0), upper := (rows 19 35 21 106 114 98 64), lower := (rows 19 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 101 85 72 80 96 64) },{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node5 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,17] 6 98 profile32_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,17] 6 98 profile32_node5_cert).mp (by decide +kernel))

def profile32_node6_cert : CutBound 7 := { lost := (rows 0 16 1 18 0 0 0), upper := (rows 19 35 22 105 113 97 64), lower := (rows 19 35 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 102 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 110 72 64 96 64) }] }

theorem profile32_node6 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,18] 6 97 profile32_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,18] 6 97 profile32_node6_cert).mp (by decide +kernel))

def profile32_node7_cert : CutBound 7 := { lost := (rows 0 16 18 1 0 0 0), upper := (rows 19 35 37 90 82 114 64), lower := (rows 19 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 85 101 101 72 80 96 64) },{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 71 103 103 72 64 96 64) }] }

theorem profile32_node7 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,33] 6 82 profile32_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,33] 6 82 profile32_node7_cert).mp (by decide +kernel))

def profile32_node8_cert : CutBound 7 := { lost := (rows 32 0 17 34 0 0 0), upper := (rows 19 35 38 89 81 113 64), lower := (rows 19 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 86 102 102 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 71 103 102 72 64 96 64) },{ target := 5, region := (rows 7 2 4 15 23 0 127), good := (rows 91 91 95 72 80 64 64) }] }

theorem profile32_node8 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,34] 6 81 profile32_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,34] 6 81 profile32_node8_cert).mp (by decide +kernel))

def profile32_node9_cert : CutBound 7 := { lost := (rows 32 16 0 48 0 0 0), upper := (rows 19 35 52 75 83 99 64), lower := (rows 19 35 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) },{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 91 84 72 80 64 64) }] }

theorem profile32_node9 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,48] 6 67 profile32_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,48] 6 67 profile32_node9_cert).mp (by decide +kernel))

def profile32_node10_cert : CutBound 7 := { lost := (rows 0 0 50 1 0 0 0), upper := (rows 19 35 69 122 114 114 64), lower := (rows 19 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 101 69 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 1 2 7 8 16 0 127), good := (rows 87 71 69 72 80 64 64) }] }

theorem profile32_node10 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,65] 6 114 profile32_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,65] 6 114 profile32_node10_cert).mp (by decide +kernel))

def profile32_node11_cert : CutBound 7 := { lost := (rows 0 0 49 2 0 0 0), upper := (rows 19 35 70 121 113 113 64), lower := (rows 19 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 102 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 71 103 70 72 64 96 64) },{ target := 5, region := (rows 1 2 7 8 16 0 127), good := (rows 87 71 70 72 80 64 64) }] }

theorem profile32_node11 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,66] 6 113 profile32_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,66] 6 113 profile32_node11_cert).mp (by decide +kernel))

def profile32_node12_cert : CutBound 7 := { lost := (rows 0 16 3 16 0 0 0), upper := (rows 19 35 84 107 115 99 64), lower := (rows 19 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 102 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 101 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node12 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,80] 6 99 profile32_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,80] 6 99 profile32_node12_cert).mp (by decide +kernel))

def profile32_node13_cert : CutBound 7 := { lost := (rows 32 0 19 32 0 0 0), upper := (rows 19 35 100 91 83 115 64), lower := (rows 19 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 86 102 100 72 80 100 64) },{ target := 1, region := (rows 1 0 38 8 16 32 127), good := (rows 85 101 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 71 103 100 72 64 100 64) },{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 91 68 72 80 64 64) }] }

theorem profile32_node13 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,96] 6 83 profile32_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33,96] 6 83 profile32_node13_cert).mp (by decide +kernel))

def profile32_node3_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node3 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,33] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile32_node3_route profile32_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node4
  · exact profile32_node5
  · exact profile32_node6
  · exact profile32_node7
  · exact profile32_node8
  · exact profile32_node9
  · exact profile32_node10
  · exact profile32_node11
  · exact profile32_node12
  · exact profile32_node13

def profile32_node14_cert : CutBound 7 := { lost := (rows 96 0 16 16 0 0 0), upper := (rows 19 50 103 107 115 99 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) },{ target := 6, region := (rows 3 2 4 8 16 32 0), good := (rows 19 51 4 8 16 32 0) }] }

theorem profile32_node14 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,48] 6 99 profile32_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,48] 6 99 profile32_node14_cert).mp (by decide +kernel))

def profile32_node16_cert : CutBound 7 := { lost := (rows 0 16 16 3 0 0 0), upper := (rows 19 67 7 120 112 112 64), lower := (rows 19 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 121 125 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile32_node16 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,3] 6 112 profile32_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,3] 6 112 profile32_node16_cert).mp (by decide +kernel))

def profile32_node17_cert : CutBound 7 := { lost := (rows 0 16 2 17 0 0 0), upper := (rows 19 67 21 106 114 98 64), lower := (rows 19 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 69 85 72 80 96 64) },{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node17 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,17] 6 98 profile32_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,17] 6 98 profile32_node17_cert).mp (by decide +kernel))

def profile32_node18_cert : CutBound 7 := { lost := (rows 0 16 1 18 0 0 0), upper := (rows 19 67 22 105 113 97 64), lower := (rows 19 67 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 86 70 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 110 72 64 96 64) }] }

theorem profile32_node18 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,18] 6 97 profile32_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,18] 6 97 profile32_node18_cert).mp (by decide +kernel))

def profile32_node19_cert : CutBound 7 := { lost := (rows 32 48 0 1 0 0 0), upper := (rows 19 67 37 122 114 114 64), lower := (rows 19 67 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 4, region := (rows 1 7 4 8 0 32 127), good := (rows 67 67 103 72 64 96 64) },{ target := 5, region := (rows 17 23 4 8 16 0 127), good := (rows 83 67 71 72 83 64 64) }] }

theorem profile32_node19 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,33] 6 114 profile32_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,33] 6 114 profile32_node19_cert).mp (by decide +kernel))

def profile32_node20_cert : CutBound 7 := { lost := (rows 32 48 0 2 0 0 0), upper := (rows 19 67 38 121 113 113 64), lower := (rows 19 67 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 102 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 70 72 83 64 64) }] }

theorem profile32_node20 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,34] 6 113 profile32_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,34] 6 113 profile32_node20_cert).mp (by decide +kernel))

def profile32_node21_cert : CutBound 7 := { lost := (rows 32 48 0 16 0 0 0), upper := (rows 19 67 52 107 115 99 64), lower := (rows 19 67 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) },{ target := 5, region := (rows 21 23 4 8 16 0 127), good := (rows 83 67 87 72 83 64 64) }] }

theorem profile32_node21 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,48] 6 99 profile32_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,48] 6 99 profile32_node21_cert).mp (by decide +kernel))

def profile32_node22_cert : CutBound 7 := { lost := (rows 0 16 18 1 0 0 0), upper := (rows 19 67 69 58 50 50 64), lower := (rows 19 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 85 69 69 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile32_node22 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,65] 6 50 profile32_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,65] 6 50 profile32_node22_cert).mp (by decide +kernel))

def profile32_node23_cert : CutBound 7 := { lost := (rows 0 16 17 2 0 0 0), upper := (rows 19 67 70 57 49 49 64), lower := (rows 19 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 86 70 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 71 71 70 72 64 96 64) }] }

theorem profile32_node23 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,66] 6 49 profile32_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,66] 6 49 profile32_node23_cert).mp (by decide +kernel))

def profile32_node24_cert : CutBound 7 := { lost := (rows 0 16 3 16 0 0 0), upper := (rows 19 67 84 43 51 35 64), lower := (rows 19 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 86 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 69 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node24 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,80] 6 35 profile32_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,80] 6 35 profile32_node24_cert).mp (by decide +kernel))

def profile32_node25_cert : CutBound 7 := { lost := (rows 0 16 19 0 0 0 0), upper := (rows 19 67 100 59 51 51 64), lower := (rows 19 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 82 66 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 81 65 100 72 80 100 64) },{ target := 4, region := (rows 1 3 36 8 0 32 127), good := (rows 67 67 100 72 64 100 64) }] }

theorem profile32_node25 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,96] 6 51 profile32_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65,96] 6 51 profile32_node25_cert).mp (by decide +kernel))

def profile32_node15_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node15_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node15 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,65] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile32_node15_route profile32_node15_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node16
  · exact profile32_node17
  · exact profile32_node18
  · exact profile32_node19
  · exact profile32_node20
  · exact profile32_node21
  · exact profile32_node22
  · exact profile32_node23
  · exact profile32_node24
  · exact profile32_node25

def profile32_node26_cert : CutBound 7 := { lost := (rows 32 33 16 16 0 0 0), upper := (rows 19 82 103 107 115 99 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 66 68 72 64 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile32_node26 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,80] 6 99 profile32_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,80] 6 99 profile32_node26_cert).mp (by decide +kernel))

def profile32_node28_cert : CutBound 7 := { lost := (rows 0 17 16 2 0 0 0), upper := (rows 19 98 7 121 113 113 64), lower := (rows 19 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 70 72 80 98 64) },{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 96 125 72 80 96 64) },{ target := 4, region := (rows 1 34 5 8 0 32 127), good := (rows 71 98 71 72 64 98 64) }] }

theorem profile32_node28 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,3] 6 113 profile32_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,3] 6 113 profile32_node28_cert).mp (by decide +kernel))

def profile32_node29_cert : CutBound 7 := { lost := (rows 0 17 2 16 0 0 0), upper := (rows 19 98 21 107 115 99 64), lower := (rows 19 98 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 84 72 80 98 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 96 85 72 80 96 64) },{ target := 4, region := (rows 1 39 4 13 0 37 127), good := (rows 107 98 111 72 64 98 64) }] }

theorem profile32_node29 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,17] 6 99 profile32_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,17] 6 99 profile32_node29_cert).mp (by decide +kernel))

def profile32_node30_cert : CutBound 7 := { lost := (rows 0 17 1 18 0 0 0), upper := (rows 19 98 22 105 113 97 64), lower := (rows 19 98 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 5 8 16 32 127), good := (rows 86 98 86 72 80 98 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 96 84 72 80 96 64) },{ target := 4, region := (rows 1 35 4 9 0 33 127), good := (rows 107 98 70 72 64 98 64) }] }

theorem profile32_node30 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,18] 6 97 profile32_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,18] 6 97 profile32_node30_cert).mp (by decide +kernel))

def profile32_node31_cert : CutBound 7 := { lost := (rows 32 17 0 32 0 0 0), upper := (rows 19 98 37 91 83 115 64), lower := (rows 19 98 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 8 16 32 127), good := (rows 82 98 102 72 80 98 64) },{ target := 4, region := (rows 1 38 4 8 0 32 127), good := (rows 67 98 103 72 64 98 64) },{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 91 93 72 80 64 64) }] }

theorem profile32_node31 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,33] 6 83 profile32_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,33] 6 83 profile32_node31_cert).mp (by decide +kernel))

def profile32_node32_cert : CutBound 7 := { lost := (rows 0 17 17 2 0 0 0), upper := (rows 19 98 38 89 81 113 64), lower := (rows 19 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 86 102 102 72 80 102 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 96 100 72 80 96 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile32_node32 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,34] 6 81 profile32_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,34] 6 81 profile32_node32_cert).mp (by decide +kernel))

def profile32_node33_cert : CutBound 7 := { lost := (rows 32 17 0 48 0 0 0), upper := (rows 19 98 52 75 83 99 64), lower := (rows 19 98 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 4 8 16 32 127), good := (rows 82 98 118 72 80 98 64) },{ target := 4, region := (rows 1 39 4 9 0 33 127), good := (rows 107 98 102 72 64 98 64) },{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 91 84 72 80 64 64) }] }

theorem profile32_node33 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,48] 6 67 profile32_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,48] 6 67 profile32_node33_cert).mp (by decide +kernel))

def profile32_node34_cert : CutBound 7 := { lost := (rows 0 17 18 0 0 0 0), upper := (rows 19 98 69 59 51 51 64), lower := (rows 19 98 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 82 98 68 72 80 98 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 85 96 69 72 80 96 64) },{ target := 4, region := (rows 1 34 5 8 0 32 127), good := (rows 71 98 69 72 64 98 64) }] }

theorem profile32_node34 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,65] 6 51 profile32_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,65] 6 51 profile32_node34_cert).mp (by decide +kernel))

def profile32_node35_cert : CutBound 7 := { lost := (rows 0 17 17 2 0 0 0), upper := (rows 19 98 70 57 49 49 64), lower := (rows 19 98 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 39 8 16 32 127), good := (rows 86 102 70 72 80 102 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 96 68 72 80 96 64) },{ target := 4, region := (rows 1 34 39 8 0 32 127), good := (rows 71 102 70 72 64 102 64) }] }

theorem profile32_node35 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,66] 6 49 profile32_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,66] 6 49 profile32_node35_cert).mp (by decide +kernel))

def profile32_node36_cert : CutBound 7 := { lost := (rows 0 17 3 16 0 0 0), upper := (rows 19 98 84 43 51 35 64), lower := (rows 19 98 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 21 8 16 32 127), good := (rows 86 98 84 72 84 98 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 85 96 84 72 84 96 64) },{ target := 4, region := (rows 1 35 4 9 0 33 127), good := (rows 107 98 68 72 64 98 64) }] }

theorem profile32_node36 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,80] 6 35 profile32_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,80] 6 35 profile32_node36_cert).mp (by decide +kernel))

def profile32_node37_cert : CutBound 7 := { lost := (rows 0 17 19 0 0 0 0), upper := (rows 19 98 100 27 19 51 64), lower := (rows 19 98 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 86 102 102 72 80 102 64) },{ target := 1, region := (rows 1 0 38 8 16 32 127), good := (rows 85 100 100 72 80 100 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile32_node37 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,96] 6 19 profile32_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96,96] 6 19 profile32_node37_cert).mp (by decide +kernel))

def profile32_node27_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node27_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node27 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18,96] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile32_node27_route profile32_node27_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node28
  · exact profile32_node29
  · exact profile32_node30
  · exact profile32_node31
  · exact profile32_node32
  · exact profile32_node33
  · exact profile32_node34
  · exact profile32_node35
  · exact profile32_node36
  · exact profile32_node37

def profile32_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node1 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile32_node1_route profile32_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node2
  · exact profile32_node3
  · exact profile32_node14
  · exact profile32_node15
  · exact profile32_node26
  · exact profile32_node27

def profile32_node39_cert : CutBound 7 := { lost := (rows 0 96 16 16 0 0 0), upper := (rows 49 19 103 107 115 99 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) },{ target := 6, region := (rows 1 3 4 8 16 32 0), good := (rows 51 19 4 8 16 32 0) }] }

theorem profile32_node39 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,17] 6 99 profile32_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,17] 6 99 profile32_node39_cert).mp (by decide +kernel))

def profile32_node40_cert : CutBound 7 := { lost := (rows 66 65 0 0 0 0 0), upper := (rows 49 50 71 75 83 99 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 114 114 68 72 80 96 64) },{ target := 1, region := (rows 3 0 4 8 16 32 127), good := (rows 113 113 68 72 80 96 64) },{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile32_node40 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,48] 6 67 profile32_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,48] 6 67 profile32_node40_cert).mp (by decide +kernel))

def profile32_node42_cert : CutBound 7 := { lost := (rows 0 48 48 1 0 0 0), upper := (rows 49 67 7 122 114 114 64), lower := (rows 49 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 112 122 126 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 87 71 71 72 80 64 64) }] }

theorem profile32_node42 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,3] 6 114 profile32_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,3] 6 114 profile32_node42_cert).mp (by decide +kernel))

def profile32_node43_cert : CutBound 7 := { lost := (rows 0 16 2 17 0 0 0), upper := (rows 49 67 21 106 114 98 64), lower := (rows 49 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 122 84 72 80 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 69 85 72 80 96 64) },{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node43 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,17] 6 98 profile32_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,17] 6 98 profile32_node43_cert).mp (by decide +kernel))

def profile32_node44_cert : CutBound 7 := { lost := (rows 0 48 32 16 0 0 0), upper := (rows 49 67 22 107 115 99 64), lower := (rows 49 67 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 110 72 64 96 64) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile32_node44 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,18] 6 99 profile32_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,18] 6 99 profile32_node44_cert).mp (by decide +kernel))

def profile32_node45_cert : CutBound 7 := { lost := (rows 2 16 3 16 0 0 0), upper := (rows 49 67 52 75 83 99 64), lower := (rows 49 67 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 116 70 116 72 80 96 64) },{ target := 1, region := (rows 5 0 5 8 16 32 127), good := (rows 117 69 117 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) }] }

theorem profile32_node45 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,48] 6 67 profile32_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,48] 6 67 profile32_node45_cert).mp (by decide +kernel))

def profile32_node46_cert : CutBound 7 := { lost := (rows 0 16 18 1 0 0 0), upper := (rows 49 67 69 58 50 50 64), lower := (rows 49 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 122 68 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 117 69 69 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile32_node46 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,65] 6 50 profile32_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,65] 6 50 profile32_node46_cert).mp (by decide +kernel))

def profile32_node47_cert : CutBound 7 := { lost := (rows 0 48 49 0 0 0 0), upper := (rows 49 67 70 59 51 51 64), lower := (rows 49 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 87 71 70 72 80 64 64) }] }

theorem profile32_node47 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,66] 6 51 profile32_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,66] 6 51 profile32_node47_cert).mp (by decide +kernel))

def profile32_node48_cert : CutBound 7 := { lost := (rows 0 16 3 16 0 0 0), upper := (rows 49 67 84 43 51 35 64), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 117 69 84 72 84 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node48 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,80] 6 35 profile32_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65,80] 6 35 profile32_node48_cert).mp (by decide +kernel))

def profile32_node41_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node41_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile32_node41 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,65] 6 (by decide) (choices 2) [3,17,18,48,65,66,80] profile32_node41_route profile32_node41_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node42
  · exact profile32_node43
  · exact profile32_node44
  · exact profile32_node45
  · exact profile32_node46
  · exact profile32_node47
  · exact profile32_node48

def profile32_node50_cert : CutBound 7 := { lost := (rows 0 33 32 16 0 0 0), upper := (rows 49 82 7 107 115 99 64), lower := (rows 49 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 97 66 111 72 64 96 64) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile32_node50 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,3] 6 99 profile32_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,3] 6 99 profile32_node50_cert).mp (by decide +kernel))

def profile32_node51_cert : CutBound 7 := { lost := (rows 0 33 18 32 0 0 0), upper := (rows 49 82 37 75 83 99 64), lower := (rows 49 82 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 102 72 82 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 80 101 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 101 72 64 96 64) },{ target := 5, region := (rows 1 23 4 13 21 0 127), good := (rows 91 82 95 72 82 64 64) }] }

theorem profile32_node51 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,33] 6 67 profile32_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,33] 6 67 profile32_node51_cert).mp (by decide +kernel))

def profile32_node52_cert : CutBound 7 := { lost := (rows 0 33 1 32 0 0 0), upper := (rows 49 82 38 75 83 99 64), lower := (rows 49 82 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 5 8 16 32 127), good := (rows 118 82 102 72 82 96 64) },{ target := 5, region := (rows 1 19 4 9 17 0 127), good := (rows 91 82 70 72 82 64 64) }] }

theorem profile32_node52 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,34] 6 67 profile32_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,34] 6 67 profile32_node52_cert).mp (by decide +kernel))

def profile32_node53_cert : CutBound 7 := { lost := (rows 0 33 50 0 0 0 0), upper := (rows 49 82 69 43 51 35 64), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 80 69 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 69 72 64 96 64) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile32_node53 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,65] 6 35 profile32_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,65] 6 35 profile32_node53_cert).mp (by decide +kernel))

def profile32_node54_cert : CutBound 7 := { lost := (rows 0 33 49 0 0 0 0), upper := (rows 49 82 70 43 51 35 64), lower := (rows 49 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 97 70 70 72 64 96 64) },{ target := 5, region := (rows 1 19 23 8 16 0 127), good := (rows 87 86 70 72 86 64 64) }] }

theorem profile32_node54 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,66] 6 35 profile32_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,66] 6 35 profile32_node54_cert).mp (by decide +kernel))

def profile32_node55_cert : CutBound 7 := { lost := (rows 0 1 19 0 0 0 0), upper := (rows 49 82 100 11 19 35 64), lower := (rows 49 82 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 37 8 16 32 127), good := (rows 118 82 100 72 82 100 64) },{ target := 1, region := (rows 1 0 37 8 16 32 127), good := (rows 117 80 100 72 80 100 64) },{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 101 66 100 72 64 100 64) }] }

theorem profile32_node55 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,96] 6 3 profile32_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80,96] 6 3 profile32_node55_cert).mp (by decide +kernel))

def profile32_node49_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile32_node49_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node49 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48,80] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile32_node49_route profile32_node49_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node50
  · exact profile32_node51
  · exact profile32_node52
  · exact profile32_node53
  · exact profile32_node54
  · exact profile32_node55

def profile32_node38_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node38_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile32_node38 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [48] 6 (by decide) (choices 2) [17,48,65,80] profile32_node38_route profile32_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile32_node39
  · exact profile32_node40
  · exact profile32_node41
  · exact profile32_node49

def profile32_node58_cert : CutBound 7 := { lost := (rows 16 0 16 3 0 0 0), upper := (rows 67 19 7 120 112 112 64), lower := (rows 67 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 122 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 121 125 120 120 120 120) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile32_node58 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,3] 6 112 profile32_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,3] 6 112 profile32_node58_cert).mp (by decide +kernel))

def profile32_node59_cert : CutBound 7 := { lost := (rows 16 0 2 17 0 0 0), upper := (rows 67 19 21 106 114 98 64), lower := (rows 67 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 69 85 85 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 109 72 64 96 64) }] }

theorem profile32_node59 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,17] 6 98 profile32_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,17] 6 98 profile32_node59_cert).mp (by decide +kernel))

def profile32_node60_cert : CutBound 7 := { lost := (rows 16 0 1 18 0 0 0), upper := (rows 67 19 22 105 113 97 64), lower := (rows 67 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 86 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 7 2 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node60 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,18] 6 97 profile32_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,18] 6 97 profile32_node60_cert).mp (by decide +kernel))

def profile32_node61_cert : CutBound 7 := { lost := (rows 48 32 0 1 0 0 0), upper := (rows 67 19 37 122 114 114 64), lower := (rows 67 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 101 72 64 96 64) },{ target := 5, region := (rows 19 18 4 8 16 0 127), good := (rows 67 83 69 72 83 64 64) }] }

theorem profile32_node61 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,33] 6 114 profile32_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,33] 6 114 profile32_node61_cert).mp (by decide +kernel))

def profile32_node62_cert : CutBound 7 := { lost := (rows 48 32 0 2 0 0 0), upper := (rows 67 19 38 121 113 113 64), lower := (rows 67 19 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 7 2 4 8 0 32 127), good := (rows 67 67 103 72 64 96 64) },{ target := 5, region := (rows 23 18 4 8 16 0 127), good := (rows 67 83 71 72 83 64 64) }] }

theorem profile32_node62 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,34] 6 113 profile32_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,34] 6 113 profile32_node62_cert).mp (by decide +kernel))

def profile32_node63_cert : CutBound 7 := { lost := (rows 48 32 0 16 0 0 0), upper := (rows 67 19 52 107 115 99 64), lower := (rows 67 19 52 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) },{ target := 5, region := (rows 23 22 4 8 16 0 127), good := (rows 67 83 87 72 83 64 64) }] }

theorem profile32_node63 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,48] 6 99 profile32_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,48] 6 99 profile32_node63_cert).mp (by decide +kernel))

def profile32_node64_cert : CutBound 7 := { lost := (rows 16 0 18 1 0 0 0), upper := (rows 67 19 69 58 50 50 64), lower := (rows 67 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 122 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 69 85 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile32_node64 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,65] 6 50 profile32_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,65] 6 50 profile32_node64_cert).mp (by decide +kernel))

def profile32_node65_cert : CutBound 7 := { lost := (rows 16 0 17 2 0 0 0), upper := (rows 67 19 70 57 49 49 64), lower := (rows 67 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 86 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 121 124 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile32_node65 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,66] 6 49 profile32_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,66] 6 49 profile32_node65_cert).mp (by decide +kernel))

def profile32_node66_cert : CutBound 7 := { lost := (rows 16 0 3 16 0 0 0), upper := (rows 67 19 84 43 51 35 64), lower := (rows 67 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 86 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 85 84 72 84 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node66 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,80] 6 35 profile32_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,80] 6 35 profile32_node66_cert).mp (by decide +kernel))

def profile32_node67_cert : CutBound 7 := { lost := (rows 16 0 19 0 0 0 0), upper := (rows 67 19 100 59 51 51 64), lower := (rows 67 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 66 82 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 65 81 100 72 80 100 64) },{ target := 4, region := (rows 3 2 36 8 0 32 127), good := (rows 67 67 100 72 64 100 64) }] }

theorem profile32_node67 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,96] 6 51 profile32_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17,96] 6 51 profile32_node67_cert).mp (by decide +kernel))

def profile32_node57_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node57_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node57 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile32_node57_route profile32_node57_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node58
  · exact profile32_node59
  · exact profile32_node60
  · exact profile32_node61
  · exact profile32_node62
  · exact profile32_node63
  · exact profile32_node64
  · exact profile32_node65
  · exact profile32_node66
  · exact profile32_node67

def profile32_node69_cert : CutBound 7 := { lost := (rows 48 0 48 2 0 0 0), upper := (rows 67 50 7 121 113 113 64), lower := (rows 67 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 112 125 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) },{ target := 5, region := (rows 7 2 7 8 16 0 127), good := (rows 71 87 71 72 80 64 64) }] }

theorem profile32_node69 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,3] 6 113 profile32_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,3] 6 113 profile32_node69_cert).mp (by decide +kernel))

def profile32_node70_cert : CutBound 7 := { lost := (rows 48 0 32 16 0 0 0), upper := (rows 67 50 21 107 115 99 64), lower := (rows 67 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 109 72 64 96 64) },{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 87 85 72 80 64 64) }] }

theorem profile32_node70 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,17] 6 99 profile32_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,17] 6 99 profile32_node70_cert).mp (by decide +kernel))

def profile32_node71_cert : CutBound 7 := { lost := (rows 16 0 1 18 0 0 0), upper := (rows 67 50 22 105 113 97 64), lower := (rows 67 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 118 86 72 80 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 112 84 72 80 96 64) },{ target := 4, region := (rows 7 2 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node71 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,18] 6 97 profile32_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,18] 6 97 profile32_node71_cert).mp (by decide +kernel))

def profile32_node72_cert : CutBound 7 := { lost := (rows 16 1 3 16 0 0 0), upper := (rows 67 50 52 75 83 99 64), lower := (rows 67 50 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 127), good := (rows 70 118 118 72 80 96 64) },{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 69 116 116 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) }] }

theorem profile32_node72 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,48] 6 67 profile32_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,48] 6 67 profile32_node72_cert).mp (by decide +kernel))

def profile32_node73_cert : CutBound 7 := { lost := (rows 48 0 50 0 0 0 0), upper := (rows 67 50 69 59 51 51 64), lower := (rows 67 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 112 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 87 69 72 80 64 64) }] }

theorem profile32_node73 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,65] 6 51 profile32_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,65] 6 51 profile32_node73_cert).mp (by decide +kernel))

def profile32_node74_cert : CutBound 7 := { lost := (rows 16 0 17 2 0 0 0), upper := (rows 67 50 70 57 49 49 64), lower := (rows 67 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 118 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 112 68 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) }] }

theorem profile32_node74 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,66] 6 49 profile32_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,66] 6 49 profile32_node74_cert).mp (by decide +kernel))

def profile32_node75_cert : CutBound 7 := { lost := (rows 16 0 3 16 0 0 0), upper := (rows 67 50 84 43 51 35 64), lower := (rows 67 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 116 84 72 84 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node75 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,80] 6 35 profile32_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48,80] 6 35 profile32_node75_cert).mp (by decide +kernel))

def profile32_node68_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node68_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile32_node68 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,48] 6 (by decide) (choices 2) [3,17,18,48,65,66,80] profile32_node68_route profile32_node68_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node69
  · exact profile32_node70
  · exact profile32_node71
  · exact profile32_node72
  · exact profile32_node73
  · exact profile32_node74
  · exact profile32_node75

def profile32_node76_cert : CutBound 7 := { lost := (rows 48 48 0 0 0 0 0), upper := (rows 67 67 55 59 51 51 64), lower := (rows 67 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 32 127), good := (rows 67 67 71 75 67 99 67) },{ target := 5, region := (rows 127 127 4 8 16 0 127), good := (rows 67 67 71 75 83 67 67) }] }

theorem profile32_node76 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,65] 6 51 profile32_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,65] 6 51 profile32_node76_cert).mp (by decide +kernel))

def profile32_node77_cert : CutBound 7 := { lost := (rows 48 33 0 0 0 0 0), upper := (rows 67 82 55 59 51 51 64), lower := (rows 67 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 66 82 68 72 82 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 19 18 4 8 16 0 127), good := (rows 67 83 68 72 83 64 64) }] }

theorem profile32_node77 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,80] 6 51 profile32_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66,80] 6 51 profile32_node77_cert).mp (by decide +kernel))

def profile32_node56_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node56_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile32_node56 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [66] 6 (by decide) (choices 2) [17,48,65,80] profile32_node56_route profile32_node56_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile32_node57
  · exact profile32_node68
  · exact profile32_node76
  · exact profile32_node77

def profile32_node79_cert : CutBound 7 := { lost := (rows 34 32 16 16 0 0 0), upper := (rows 81 19 103 107 115 99 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 81 68 72 81 96 64) },{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile32_node79 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,17] 6 99 profile32_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,17] 6 99 profile32_node79_cert).mp (by decide +kernel))

def profile32_node81_cert : CutBound 7 := { lost := (rows 34 0 48 1 0 0 0), upper := (rows 81 35 7 122 114 114 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 80 122 126 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 97 69 72 81 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 71 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 71 72 81 64 64) }] }

theorem profile32_node81 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,3] 6 114 profile32_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,3] 6 114 profile32_node81_cert).mp (by decide +kernel))

def profile32_node82_cert : CutBound 7 := { lost := (rows 2 16 2 17 0 0 0), upper := (rows 81 35 21 106 114 98 64), lower := (rows 81 35 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 84 72 80 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) },{ target := 4, region := (rows 1 7 4 15 0 39 127), good := (rows 107 107 111 72 64 96 64) }] }

theorem profile32_node82 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,17] 6 98 profile32_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,17] 6 98 profile32_node82_cert).mp (by decide +kernel))

def profile32_node83_cert : CutBound 7 := { lost := (rows 34 16 0 16 0 0 0), upper := (rows 81 35 22 107 115 99 64), lower := (rows 81 35 22 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 8 16 32 127), good := (rows 81 97 85 72 81 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 110 72 64 96 64) },{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 67 87 72 81 64 64) }] }

theorem profile32_node83 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,18] 6 99 profile32_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,18] 6 99 profile32_node83_cert).mp (by decide +kernel))

def profile32_node84_cert : CutBound 7 := { lost := (rows 2 16 18 1 0 0 0), upper := (rows 81 35 37 90 82 114 64), lower := (rows 81 35 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 100 72 80 96 64) },{ target := 1, region := (rows 17 0 6 8 16 32 127), good := (rows 81 101 101 72 81 96 64) },{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 65 103 103 72 64 96 64) }] }

theorem profile32_node84 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,33] 6 82 profile32_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,33] 6 82 profile32_node84_cert).mp (by decide +kernel))

def profile32_node85_cert : CutBound 7 := { lost := (rows 34 0 17 32 0 0 0), upper := (rows 81 35 38 91 83 115 64), lower := (rows 81 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 102 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 97 100 72 81 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 102 72 64 96 64) },{ target := 5, region := (rows 23 2 4 14 22 0 127), good := (rows 81 91 95 72 81 64 64) }] }

theorem profile32_node85 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,34] 6 83 profile32_node85_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,34] 6 83 profile32_node85_cert).mp (by decide +kernel))

def profile32_node86_cert : CutBound 7 := { lost := (rows 34 16 0 48 0 0 0), upper := (rows 81 35 52 75 83 99 64), lower := (rows 81 35 52 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 8 16 32 127), good := (rows 81 97 117 72 81 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 100 72 64 96 64) },{ target := 5, region := (rows 23 2 4 10 18 0 127), good := (rows 81 91 85 72 81 64 64) }] }

theorem profile32_node86 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,48] 6 67 profile32_node86_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,48] 6 67 profile32_node86_cert).mp (by decide +kernel))

def profile32_node87_cert : CutBound 7 := { lost := (rows 2 0 18 1 0 0 0), upper := (rows 81 35 69 58 50 50 64), lower := (rows 81 35 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 122 68 72 80 96 64) },{ target := 1, region := (rows 17 0 23 8 16 32 127), good := (rows 85 101 69 72 85 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 69 103 69 72 64 96 64) }] }

theorem profile32_node87 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,65] 6 50 profile32_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,65] 6 50 profile32_node87_cert).mp (by decide +kernel))

def profile32_node88_cert : CutBound 7 := { lost := (rows 34 0 49 0 0 0 0), upper := (rows 81 35 70 59 51 51 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 97 68 72 81 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 70 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 70 72 81 64 64) }] }

theorem profile32_node88 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,66] 6 51 profile32_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,66] 6 51 profile32_node88_cert).mp (by decide +kernel))

def profile32_node89_cert : CutBound 7 := { lost := (rows 2 16 3 16 0 0 0), upper := (rows 81 35 84 43 51 35 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 107 107 68 72 64 96 64) }] }

theorem profile32_node89 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,80] 6 35 profile32_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,80] 6 35 profile32_node89_cert).mp (by decide +kernel))

def profile32_node90_cert : CutBound 7 := { lost := (rows 2 0 19 0 0 0 0), upper := (rows 81 35 100 27 19 51 64), lower := (rows 81 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 102 100 72 80 100 64) },{ target := 1, region := (rows 17 0 38 8 16 32 127), good := (rows 81 101 100 72 81 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 103 100 72 64 100 64) }] }

theorem profile32_node90 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,96] 6 19 profile32_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33,96] 6 19 profile32_node90_cert).mp (by decide +kernel))

def profile32_node80_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node80_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node80 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile32_node80_route profile32_node80_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node81
  · exact profile32_node82
  · exact profile32_node83
  · exact profile32_node84
  · exact profile32_node85
  · exact profile32_node86
  · exact profile32_node87
  · exact profile32_node88
  · exact profile32_node89
  · exact profile32_node90

def profile32_node92_cert : CutBound 7 := { lost := (rows 34 0 32 16 0 0 0), upper := (rows 81 50 7 107 115 99 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 113 69 72 81 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 98 111 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile32_node92 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,3] 6 99 profile32_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,3] 6 99 profile32_node92_cert).mp (by decide +kernel))

def profile32_node93_cert : CutBound 7 := { lost := (rows 34 0 2 32 0 0 0), upper := (rows 81 50 37 75 83 99 64), lower := (rows 81 50 37 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 6 8 16 32 127), good := (rows 81 117 101 72 81 96 64) },{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 91 69 72 81 64 64) }] }

theorem profile32_node93 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,33] 6 67 profile32_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,33] 6 67 profile32_node93_cert).mp (by decide +kernel))

def profile32_node94_cert : CutBound 7 := { lost := (rows 34 0 17 32 0 0 0), upper := (rows 81 50 38 75 83 99 64), lower := (rows 81 50 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 102 72 80 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 113 101 72 81 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 102 72 64 96 64) },{ target := 5, region := (rows 23 2 4 14 22 0 127), good := (rows 81 91 95 72 81 64 64) }] }

theorem profile32_node94 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,34] 6 67 profile32_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,34] 6 67 profile32_node94_cert).mp (by decide +kernel))

def profile32_node95_cert : CutBound 7 := { lost := (rows 34 0 50 0 0 0 0), upper := (rows 81 50 69 43 51 35 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 32 127), good := (rows 85 117 69 72 85 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 98 69 72 64 96 64) },{ target := 5, region := (rows 19 2 23 8 16 0 127), good := (rows 85 87 69 72 85 64 64) }] }

theorem profile32_node95 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,65] 6 35 profile32_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,65] 6 35 profile32_node95_cert).mp (by decide +kernel))

def profile32_node96_cert : CutBound 7 := { lost := (rows 34 0 49 0 0 0 0), upper := (rows 81 50 70 43 51 35 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 113 69 72 81 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 70 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile32_node96 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,66] 6 35 profile32_node96_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,66] 6 35 profile32_node96_cert).mp (by decide +kernel))

def profile32_node97_cert : CutBound 7 := { lost := (rows 2 0 19 0 0 0 0), upper := (rows 81 50 100 11 19 35 64), lower := (rows 81 50 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 118 100 72 80 100 64) },{ target := 1, region := (rows 19 0 38 8 16 32 127), good := (rows 81 117 100 72 81 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 102 100 72 64 100 64) }] }

theorem profile32_node97 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,96] 6 3 profile32_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48,96] 6 3 profile32_node97_cert).mp (by decide +kernel))

def profile32_node91_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile32_node91_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node91 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,48] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile32_node91_route profile32_node91_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node92
  · exact profile32_node93
  · exact profile32_node94
  · exact profile32_node95
  · exact profile32_node96
  · exact profile32_node97

def profile32_node98_cert : CutBound 7 := { lost := (rows 34 48 0 0 0 0 0), upper := (rows 81 67 55 59 51 51 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 65 68 72 81 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile32_node98 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,65] 6 51 profile32_node98_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,65] 6 51 profile32_node98_cert).mp (by decide +kernel))

def profile32_node99_cert : CutBound 7 := { lost := (rows 34 33 0 0 0 0 0), upper := (rows 81 82 39 43 51 35 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 81 68 72 81 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile32_node99 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,80] 6 35 profile32_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,80] 6 35 profile32_node99_cert).mp (by decide +kernel))

def profile32_node100_cert : CutBound 7 := { lost := (rows 34 17 0 0 0 0 0), upper := (rows 81 98 55 59 51 51 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 96 68 72 81 96 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 65 98 68 72 64 98 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 66 68 72 81 64 64) }] }

theorem profile32_node100 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,96] 6 51 profile32_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80,96] 6 51 profile32_node100_cert).mp (by decide +kernel))

def profile32_node78_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node78_route : Route 7 := (fun mask => (mask,id))

theorem profile32_node78 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile32_node78_route profile32_node78_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile32_node79
  · exact profile32_node80
  · exact profile32_node91
  · exact profile32_node98
  · exact profile32_node99
  · exact profile32_node100

def profile32_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile32_node0_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile32_node0 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [] 6 (by decide) (choices 2) [18,48,66,80] profile32_node0_route profile32_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile32_node1
  · exact profile32_node38
  · exact profile32_node56
  · exact profile32_node78

theorem profile32 : Upper (D (n:=7) [34,34,32,32,18,18,2]) (R (n:=7) [34,34,32,32,18,18,2]) [] 6 := profile32_node0


#print axioms profile32
end Delivery.SmallBudgetTenFinite7
