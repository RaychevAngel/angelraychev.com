import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile11_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 19 101 105 113 32 64), lower := (rows 23 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile11_node2 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,17] 6 97 profile11_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,17] 6 97 profile11_node2_cert).mp (by decide +kernel))

def profile11_node3_cert : CutBound 7 := { lost := (rows 0 80 0 0 0 0 0), upper := (rows 23 35 117 121 113 32 64), lower := (rows 23 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) },{ target := 6, region := (rows 1 3 4 8 16 127 0), good := (rows 55 35 36 40 48 32 32) }] }

theorem profile11_node3 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,33] 6 113 profile11_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,33] 6 113 profile11_node3_cert).mp (by decide +kernel))

def profile11_node4_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 23 50 101 105 113 32 64), lower := (rows 23 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 118 114 100 104 114 96 96) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile11_node4 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,48] 6 97 profile11_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,48] 6 97 profile11_node4_cert).mp (by decide +kernel))

def profile11_node5_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 23 98 117 121 113 32 64), lower := (rows 23 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 118 98 102 106 114 98 98) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 103 98 102 106 98 98 98) }] }

theorem profile11_node5 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,96] 6 113 profile11_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22,96] 6 113 profile11_node5_cert).mp (by decide +kernel))

def profile11_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node1_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node1 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [22] 6 (by decide) (choices 2) [17,33,48,96] profile11_node1_route profile11_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node2
  · exact profile11_node3
  · exact profile11_node4
  · exact profile11_node5

def profile11_node8_cert : CutBound 7 := { lost := (rows 0 0 0 17 0 0 0), upper := (rows 39 19 21 104 112 32 64), lower := (rows 39 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 111 107 109 104 104 104 104) }] }

theorem profile11_node8 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,17] 6 96 profile11_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,17] 6 96 profile11_node8_cert).mp (by decide +kernel))

def profile11_node9_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 39 19 37 88 80 32 64), lower := (rows 39 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile11_node9 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,33] 6 80 profile11_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,33] 6 80 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 39 19 52 73 81 32 64), lower := (rows 39 19 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 127 127), good := (rows 102 118 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 111 107 100 104 96 96 96) }] }

theorem profile11_node10 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,48] 6 65 profile11_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,48] 6 65 profile11_node10_cert).mp (by decide +kernel))

def profile11_node11_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 39 19 69 120 112 32 64), lower := (rows 39 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 126 122 124 120 120 120 120) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile11_node11 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,65] 6 112 profile11_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,65] 6 112 profile11_node11_cert).mp (by decide +kernel))

def profile11_node12_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 39 19 84 105 113 32 64), lower := (rows 39 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 127 127), good := (rows 102 118 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 111 107 100 104 96 96 96) }] }

theorem profile11_node12 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,80] 6 97 profile11_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,80] 6 97 profile11_node12_cert).mp (by decide +kernel))

def profile11_node13_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 39 19 100 89 81 32 64), lower := (rows 39 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 118 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile11_node13 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,96] 6 81 profile11_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17,96] 6 81 profile11_node13_cert).mp (by decide +kernel))

def profile11_node7_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node7_route : Route 7 := (fun mask => (mask,id))

theorem profile11_node7 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,17] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile11_node7_route profile11_node7_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node8
  · exact profile11_node9
  · exact profile11_node10
  · exact profile11_node11
  · exact profile11_node12
  · exact profile11_node13

def profile11_node14_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 35 85 89 81 32 64), lower := (rows 39 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile11_node14 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,33] 6 81 profile11_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,33] 6 81 profile11_node14_cert).mp (by decide +kernel))

def profile11_node15_cert : CutBound 7 := { lost := (rows 0 1 32 32 0 0 0), upper := (rows 39 50 85 89 81 32 64), lower := (rows 39 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 102 114 100 104 114 96 96) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile11_node15 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,48] 6 81 profile11_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,48] 6 81 profile11_node15_cert).mp (by decide +kernel))

def profile11_node16_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 39 67 117 121 113 32 64), lower := (rows 39 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 5 7 4 8 0 127 127), good := (rows 103 99 103 104 96 96 96) }] }

theorem profile11_node16 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,65] 6 113 profile11_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,65] 6 113 profile11_node16_cert).mp (by decide +kernel))

def profile11_node17_cert : CutBound 7 := { lost := (rows 0 33 0 0 0 0 0), upper := (rows 39 82 117 121 113 32 64), lower := (rows 39 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 102 114 100 104 114 96 96) },{ target := 5, region := (rows 1 18 4 8 16 0 127), good := (rows 71 82 68 72 82 64 64) }] }

theorem profile11_node17 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,80] 6 113 profile11_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,80] 6 113 profile11_node17_cert).mp (by decide +kernel))

def profile11_node18_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 39 98 85 89 81 32 64), lower := (rows 39 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 4, region := (rows 5 127 4 8 0 127 127), good := (rows 103 98 103 106 98 98 98) }] }

theorem profile11_node18 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,96] 6 81 profile11_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38,96] 6 81 profile11_node18_cert).mp (by decide +kernel))

def profile11_node6_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node6_route : Route 7 := (fun mask => (mask,id))

theorem profile11_node6 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [38] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile11_node6_route profile11_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node7
  · exact profile11_node14
  · exact profile11_node15
  · exact profile11_node16
  · exact profile11_node17
  · exact profile11_node18

def profile11_node21_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 51 7 21 104 112 32 64), lower := (rows 51 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 6 4 127 0 127 127), good := (rows 107 111 111 104 104 104 104) }] }

theorem profile11_node21 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,17] 6 96 profile11_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,17] 6 96 profile11_node21_cert).mp (by decide +kernel))

def profile11_node22_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 51 7 37 88 80 32 64), lower := (rows 51 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile11_node22 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,33] 6 80 profile11_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,33] 6 80 profile11_node22_cert).mp (by decide +kernel))

def profile11_node23_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 51 7 52 73 81 32 64), lower := (rows 51 7 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 127 127), good := (rows 118 102 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 107 111 100 104 96 96 96) }] }

theorem profile11_node23 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,48] 6 65 profile11_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,48] 6 65 profile11_node23_cert).mp (by decide +kernel))

def profile11_node24_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 51 7 69 120 112 32 64), lower := (rows 51 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 124 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile11_node24 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,65] 6 112 profile11_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,65] 6 112 profile11_node24_cert).mp (by decide +kernel))

def profile11_node25_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 51 7 84 105 113 32 64), lower := (rows 51 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 127 127), good := (rows 118 102 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 107 111 100 104 96 96 96) }] }

theorem profile11_node25 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,80] 6 97 profile11_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,80] 6 97 profile11_node25_cert).mp (by decide +kernel))

def profile11_node26_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 51 7 100 89 81 32 64), lower := (rows 51 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 118 102 100 108 116 100 100) },{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile11_node26 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,96] 6 81 profile11_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5,96] 6 81 profile11_node26_cert).mp (by decide +kernel))

def profile11_node20_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node20_route : Route 7 := (fun mask => (mask,id))

theorem profile11_node20 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,5] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile11_node20_route profile11_node20_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node21
  · exact profile11_node22
  · exact profile11_node23
  · exact profile11_node24
  · exact profile11_node25
  · exact profile11_node26

def profile11_node27_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 19 101 109 117 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile11_node27 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,17] 6 101 profile11_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,17] 6 101 profile11_node27_cert).mp (by decide +kernel))

def profile11_node28_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 22 101 105 113 32 64), lower := (rows 51 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 102 100 104 96 96 96) }] }

theorem profile11_node28 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,20] 6 97 profile11_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,20] 6 97 profile11_node28_cert).mp (by decide +kernel))

def profile11_node29_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 51 35 85 93 85 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 7 11 19 0 127), good := (rows 95 95 68 72 80 64 64) }] }

theorem profile11_node29 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,33] 6 85 profile11_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,33] 6 85 profile11_node29_cert).mp (by decide +kernel))

def profile11_node30_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 51 38 85 89 81 32 64), lower := (rows 51 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 114 102 102 104 112 96 96) },{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) }] }

theorem profile11_node30 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,36] 6 81 profile11_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,36] 6 81 profile11_node30_cert).mp (by decide +kernel))

def profile11_node31_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 51 50 69 77 85 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile11_node31 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,48] 6 69 profile11_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,48] 6 69 profile11_node31_cert).mp (by decide +kernel))

def profile11_node32_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 51 67 117 125 117 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile11_node32 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,65] 6 117 profile11_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,65] 6 117 profile11_node32_cert).mp (by decide +kernel))

def profile11_node33_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 51 70 117 121 113 32 64), lower := (rows 51 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 114 102 102 104 112 96 96) },{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 99 102 102 104 96 96 96) }] }

theorem profile11_node33 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,68] 6 113 profile11_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,68] 6 113 profile11_node33_cert).mp (by decide +kernel))

def profile11_node34_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 51 82 101 109 117 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile11_node34 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,80] 6 101 profile11_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,80] 6 101 profile11_node34_cert).mp (by decide +kernel))

def profile11_node35_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 51 98 85 93 85 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile11_node35 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,96] 6 85 profile11_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50,96] 6 85 profile11_node35_cert).mp (by decide +kernel))

def profile11_node19_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node19_route : Route 7 := (fun mask => (mask,id))

theorem profile11_node19 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [50] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile11_node19_route profile11_node19_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node20
  · exact profile11_node27
  · exact profile11_node28
  · exact profile11_node29
  · exact profile11_node30
  · exact profile11_node31
  · exact profile11_node32
  · exact profile11_node33
  · exact profile11_node34
  · exact profile11_node35

def profile11_node37_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 7 117 121 113 32 64), lower := (rows 99 7 4 8 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 127 127), good := (rows 99 103 103 104 96 96 96) }] }

theorem profile11_node37 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,5] 6 113 profile11_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,5] 6 113 profile11_node37_cert).mp (by decide +kernel))

def profile11_node39_cert : CutBound 7 := { lost := (rows 16 0 0 17 0 0 0), upper := (rows 99 19 21 108 116 32 64), lower := (rows 99 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 127 127), good := (rows 98 114 124 104 112 96 96) },{ target := 4, region := (rows 3 2 4 12 0 127 127), good := (rows 99 99 109 104 96 96 96) }] }

theorem profile11_node39 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,17] 6 100 profile11_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,17] 6 100 profile11_node39_cert).mp (by decide +kernel))

def profile11_node40_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 99 19 37 92 84 32 64), lower := (rows 99 19 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 127 127), good := (rows 98 114 124 104 112 96 96) },{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile11_node40 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,33] 6 84 profile11_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,33] 6 84 profile11_node40_cert).mp (by decide +kernel))

def profile11_node41_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 99 19 52 77 85 32 64), lower := (rows 99 19 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 127 127), good := (rows 102 118 116 104 116 96 96) },{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile11_node41 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,48] 6 69 profile11_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,48] 6 69 profile11_node41_cert).mp (by decide +kernel))

def profile11_node42_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 99 19 100 29 21 32 64), lower := (rows 99 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 102 118 100 108 116 100 100) },{ target := 4, region := (rows 3 2 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile11_node42 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,96] 6 21 profile11_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17,96] 6 21 profile11_node42_cert).mp (by decide +kernel))

def profile11_node38_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node38_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node38 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,17] 6 (by decide) (choices 2) [17,33,48,96] profile11_node38_route profile11_node38_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node39
  · exact profile11_node40
  · exact profile11_node41
  · exact profile11_node42

def profile11_node44_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 99 22 21 105 113 32 64), lower := (rows 99 22 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 118 118 104 112 96 96) },{ target := 4, region := (rows 3 2 4 15 0 127 127), good := (rows 107 111 109 104 96 96 96) }] }

theorem profile11_node44 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,17] 6 97 profile11_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,17] 6 97 profile11_node44_cert).mp (by decide +kernel))

def profile11_node45_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 99 22 37 89 81 32 64), lower := (rows 99 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 127 127), good := (rows 103 103 101 104 96 96 96) }] }

theorem profile11_node45 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,33] 6 81 profile11_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,33] 6 81 profile11_node45_cert).mp (by decide +kernel))

def profile11_node46_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 99 22 52 73 81 32 64), lower := (rows 99 22 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 127 127), good := (rows 102 118 118 104 118 96 96) }] }

theorem profile11_node46 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,48] 6 65 profile11_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,48] 6 65 profile11_node46_cert).mp (by decide +kernel))

def profile11_node47_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 99 22 100 25 17 32 64), lower := (rows 99 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 127 8 16 127 127), good := (rows 102 118 100 108 118 100 100) }] }

theorem profile11_node47 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,96] 6 17 profile11_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20,96] 6 17 profile11_node47_cert).mp (by decide +kernel))

def profile11_node43_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node43_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node43 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,20] 6 (by decide) (choices 2) [17,33,48,96] profile11_node43_route profile11_node43_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node44
  · exact profile11_node45
  · exact profile11_node46
  · exact profile11_node47

def profile11_node48_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 99 35 85 93 85 32 64), lower := (rows 99 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) }] }

theorem profile11_node48 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,33] 6 85 profile11_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,33] 6 85 profile11_node48_cert).mp (by decide +kernel))

def profile11_node49_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 99 38 85 89 81 32 64), lower := (rows 99 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 98 102 102 104 112 96 96) },{ target := 4, region := (rows 7 6 4 8 0 127 127), good := (rows 99 103 103 104 96 96 96) }] }

theorem profile11_node49 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,36] 6 81 profile11_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,36] 6 81 profile11_node49_cert).mp (by decide +kernel))

def profile11_node50_cert : CutBound 7 := { lost := (rows 16 1 0 0 0 0 0), upper := (rows 99 50 85 93 85 32 64), lower := (rows 99 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 127 127), good := (rows 98 114 100 104 114 96 96) },{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile11_node50 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,48] 6 85 profile11_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,48] 6 85 profile11_node50_cert).mp (by decide +kernel))

def profile11_node51_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 99 98 21 29 21 32 64), lower := (rows 99 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 4, region := (rows 127 127 4 8 0 127 127), good := (rows 99 99 103 107 99 99 99) }] }

theorem profile11_node51 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,96] 6 21 profile11_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98,96] 6 21 profile11_node51_cert).mp (by decide +kernel))

def profile11_node36_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node36_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node36 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [98] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile11_node36_route profile11_node36_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node37
  · exact profile11_node38
  · exact profile11_node43
  · exact profile11_node48
  · exact profile11_node49
  · exact profile11_node50
  · exact profile11_node51

def profile11_node54_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 113 7 7 120 112 32 64), lower := (rows 113 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile11_node54 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,3] 6 112 profile11_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,3] 6 112 profile11_node54_cert).mp (by decide +kernel))

def profile11_node55_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 113 7 21 106 114 32 64), lower := (rows 113 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 112 126 116 104 112 96 96) },{ target := 4, region := (rows 1 6 4 14 0 127 127), good := (rows 97 111 111 104 96 96 96) }] }

theorem profile11_node55 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,17] 6 98 profile11_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,17] 6 98 profile11_node55_cert).mp (by decide +kernel))

def profile11_node56_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 113 7 22 105 113 32 64), lower := (rows 113 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 127 127), good := (rows 105 111 110 104 96 96 96) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile11_node56 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,18] 6 97 profile11_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,18] 6 97 profile11_node56_cert).mp (by decide +kernel))

def profile11_node57_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 113 7 37 90 82 32 64), lower := (rows 113 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 112 126 100 104 112 96 96) },{ target := 4, region := (rows 1 7 7 8 0 127 127), good := (rows 103 103 103 104 96 96 96) }] }

theorem profile11_node57 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,33] 6 82 profile11_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,33] 6 82 profile11_node57_cert).mp (by decide +kernel))

def profile11_node58_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 113 7 38 89 81 32 64), lower := (rows 113 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 112 102 102 104 112 96 96) },{ target := 4, region := (rows 1 3 7 8 0 127 127), good := (rows 103 103 102 104 96 96 96) }] }

theorem profile11_node58 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,34] 6 81 profile11_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,34] 6 81 profile11_node58_cert).mp (by decide +kernel))

def profile11_node59_cert : CutBound 7 := { lost := (rows 0 0 1 16 0 0 0), upper := (rows 113 7 52 75 83 32 64), lower := (rows 113 7 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 127 127), good := (rows 116 102 116 104 116 96 96) },{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile11_node59 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,48] 6 67 profile11_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,48] 6 67 profile11_node59_cert).mp (by decide +kernel))

def profile11_node60_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 113 7 100 27 19 32 64), lower := (rows 113 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 116 102 100 108 116 100 100) },{ target := 4, region := (rows 1 3 127 8 0 127 127), good := (rows 103 103 100 108 100 100 100) }] }

theorem profile11_node60 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,96] 6 19 profile11_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5,96] 6 19 profile11_node60_cert).mp (by decide +kernel))

def profile11_node53_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node53_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node53 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,5] 6 (by decide) (choices 2) [3,17,18,33,34,48,96] profile11_node53_route profile11_node53_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node54
  · exact profile11_node55
  · exact profile11_node56
  · exact profile11_node57
  · exact profile11_node58
  · exact profile11_node59
  · exact profile11_node60

def profile11_node61_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 19 103 111 119 32 64), lower := (rows 113 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile11_node61 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,17] 6 103 profile11_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,17] 6 103 profile11_node61_cert).mp (by decide +kernel))

def profile11_node63_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 113 22 7 105 113 32 64), lower := (rows 113 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 127 127), good := (rows 105 110 111 104 96 96 96) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 86 71 72 80 64 64) }] }

theorem profile11_node63 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,3] 6 97 profile11_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,3] 6 97 profile11_node63_cert).mp (by decide +kernel))

def profile11_node64_cert : CutBound 7 := { lost := (rows 0 32 16 32 0 0 0), upper := (rows 113 22 37 75 83 32 64), lower := (rows 113 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 101 102 101 104 96 96 96) },{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 81 94 95 72 80 64 64) }] }

theorem profile11_node64 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,33] 6 67 profile11_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,33] 6 67 profile11_node64_cert).mp (by decide +kernel))

def profile11_node65_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 113 22 38 73 81 32 64), lower := (rows 113 22 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 127 127), good := (rows 118 118 102 104 118 96 96) }] }

theorem profile11_node65 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,34] 6 65 profile11_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,34] 6 65 profile11_node65_cert).mp (by decide +kernel))

def profile11_node66_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 113 22 100 11 19 32 64), lower := (rows 113 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 127 8 16 127 127), good := (rows 118 118 100 108 118 100 100) }] }

theorem profile11_node66 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,96] 6 3 profile11_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20,96] 6 3 profile11_node66_cert).mp (by decide +kernel))

def profile11_node62_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile11_node62_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node62 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,20] 6 (by decide) (choices 2) [3,33,34,96] profile11_node62_route profile11_node62_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node63
  · exact profile11_node64
  · exact profile11_node65
  · exact profile11_node66

def profile11_node67_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 113 35 87 95 87 32 64), lower := (rows 113 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 81 95 68 72 80 64 64) }] }

theorem profile11_node67 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,33] 6 87 profile11_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,33] 6 87 profile11_node67_cert).mp (by decide +kernel))

def profile11_node68_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 113 38 87 91 83 32 64), lower := (rows 113 38 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 112 102 102 104 112 96 96) },{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 97 102 102 104 96 96 96) }] }

theorem profile11_node68 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,36] 6 83 profile11_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,36] 6 83 profile11_node68_cert).mp (by decide +kernel))

def profile11_node69_cert : CutBound 7 := { lost := (rows 0 65 0 0 0 0 0), upper := (rows 113 50 71 79 87 32 64), lower := (rows 113 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) },{ target := 6, region := (rows 1 19 4 8 16 127 0), good := (rows 51 50 36 40 50 32 32) }] }

theorem profile11_node69 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,48] 6 71 profile11_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,48] 6 71 profile11_node69_cert).mp (by decide +kernel))

def profile11_node70_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 113 98 23 31 23 32 64), lower := (rows 113 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) },{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile11_node70 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,96] 6 23 profile11_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112,96] 6 23 profile11_node70_cert).mp (by decide +kernel))

def profile11_node52_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile11_node52_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node52 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [112] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile11_node52_route profile11_node52_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node53
  · exact profile11_node61
  · exact profile11_node62
  · exact profile11_node67
  · exact profile11_node68
  · exact profile11_node69
  · exact profile11_node70

def profile11_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile11_node0_route : Route 7 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 100 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile11_node0 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [] 6 (by decide) (choices 3) [22,38,50,98,112] profile11_node0_route profile11_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile11_node1
  · exact profile11_node6
  · exact profile11_node19
  · exact profile11_node36
  · exact profile11_node52

theorem profile11 : Upper (D (n:=7) [50,33,33,32,18,2,2]) (R (n:=7) [50,33,33,32,18,2,2]) [] 6 := profile11_node0


#print axioms profile11
end Delivery.SmallBudgetTenFinite7
