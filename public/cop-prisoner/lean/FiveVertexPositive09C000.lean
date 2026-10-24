import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive09
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,5] 3 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,5] 3 profile0_node2_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 7 11 7 28 28), lower := (rows 7 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile0_node4 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,3] 3 profile0_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,3] 3 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 7 11 13 30 22), lower := (rows 7 11 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 13 13 8 16) }] }

theorem profile0_node5 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,9] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,9] 3 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,9] 3 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 7 11 14 29 21), lower := (rows 7 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 14 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) }] }

theorem profile0_node6 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,10] 3 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,10] 3 profile0_node6_cert).mp (by decide +kernel))

def profile0_node8_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 7 11 21 14 24), lower := (rows 7 11 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 31), good := (rows 30 26 28 30 16) },{ target := 1, region := (rows 1 0 7 8 26), good := (rows 21 29 21 28 16) }] }

theorem profile0_node8 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17,6] 3 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17,6] 3 profile0_node8_cert).mp (by decide +kernel))

def profile0_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node7 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17] 3 (by decide) (choices 2) [6] profile0_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,17] (choices 2) [6] profile0_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node8

def profile0_node9_cert : CutBound 5 := { lost := (rows 8 0 0 2 0), upper := (rows 7 11 22 13 29), lower := (rows 7 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 7 3 23 0 16) }] }

theorem profile0_node9 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,18] 3 profile0_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,18] 3 profile0_node9_cert).mp (by decide +kernel))

def profile0_node11_cert : CutBound 5 := { lost := (rows 0 0 3 0 0), upper := (rows 7 11 28 11 20), lower := (rows 7 11 28 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 31), good := (rows 22 30 28 30 16) },{ target := 1, region := (rows 1 0 14 8 31), good := (rows 21 29 28 29 16) }] }

theorem profile0_node11 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,3] 3 profile0_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,3] 3 profile0_node11_cert).mp (by decide +kernel))

def profile0_node12_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 7 11 28 13 18), lower := (rows 7 11 28 13 16), losses := [{ target := 0, region := (rows 0 2 14 8 19), good := (rows 22 30 28 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 13 9 28 13 16) }] }

theorem profile0_node12 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,5] 3 profile0_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,5] 3 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 7 11 28 14 17), lower := (rows 7 11 28 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 10 28 14 16) },{ target := 1, region := (rows 1 0 14 8 19), good := (rows 21 29 28 28 16) }] }

theorem profile0_node13 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,6] 3 profile0_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24,6] 3 profile0_node13_cert).mp (by decide +kernel))

def profile0_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node10 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24] 3 (by decide) (choices 2) [3,5,6] profile0_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9,24] (choices 2) [3,5,6] profile0_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node11
  · exact profile0_node12
  · exact profile0_node13

def profile0_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile0_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,9] (choices 2) [3,9,10,17,18,24] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7
  · exact profile0_node9
  · exact profile0_node10

def profile0_node14_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 7 14 31 27 27), lower := (rows 7 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile0_node14 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,12] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,12] 3 profile0_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,12] 3 profile0_node14_cert).mp (by decide +kernel))

def profile0_node17_cert : CutBound 5 := { lost := (rows 0 4 0 1 0), upper := (rows 7 19 13 14 24), lower := (rows 7 19 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 31), good := (rows 30 26 28 30 16) },{ target := 2, region := (rows 1 7 0 8 28), good := (rows 19 19 27 26 16) }] }

theorem profile0_node17 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9,6] 3 profile0_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9,6] 3 profile0_node17_cert).mp (by decide +kernel))

def profile0_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node16 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9] 3 (by decide) (choices 2) [6] profile0_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,9] (choices 2) [6] profile0_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node17

def profile0_node18_cert : CutBound 5 := { lost := (rows 8 0 0 2 0), upper := (rows 7 19 14 13 29), lower := (rows 7 19 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 7 19 7 0 16) }] }

theorem profile0_node18 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,10] 3 profile0_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17,10] 3 profile0_node18_cert).mp (by decide +kernel))

def profile0_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node15 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17] 3 (by decide) (choices 2) [9,10] profile0_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,17] (choices 2) [9,10] profile0_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node16
  · exact profile0_node18

def profile0_node19_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 7 22 15 11 27), lower := (rows 7 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 7 23 4 0 16) }] }

theorem profile0_node19 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,20] 3 profile0_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,20] 3 profile0_node19_cert).mp (by decide +kernel))

def profile0_node21_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 7 26 7 13 29), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile0_node21 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,3] 3 profile0_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,3] 3 profile0_node21_cert).mp (by decide +kernel))

def profile0_node23_cert : CutBound 5 := { lost := (rows 0 1 2 0 0), upper := (rows 7 26 13 11 20), lower := (rows 7 26 13 11 16), losses := [{ target := 0, region := (rows 0 14 4 8 21), good := (rows 22 26 30 26 16) },{ target := 1, region := (rows 1 0 12 8 31), good := (rows 21 28 29 29 16) }] }

theorem profile0_node23 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,3] 3 profile0_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,3] 3 profile0_node23_cert).mp (by decide +kernel))

def profile0_node24_cert : CutBound 5 := { lost := (rows 0 1 2 2 0), upper := (rows 7 26 13 13 18), lower := (rows 7 26 13 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 31), good := (rows 22 26 30 30 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 28 13 13 16) }] }

theorem profile0_node24 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,5] 3 profile0_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,5] 3 profile0_node24_cert).mp (by decide +kernel))

def profile0_node25_cert : CutBound 5 := { lost := (rows 0 4 0 1 0), upper := (rows 7 26 13 14 17), lower := (rows 7 26 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 12 14 16) },{ target := 2, region := (rows 1 14 0 8 21), good := (rows 19 26 27 26 16) }] }

theorem profile0_node25 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,6] 3 profile0_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9,6] 3 profile0_node25_cert).mp (by decide +kernel))

def profile0_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node22 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9] 3 (by decide) (choices 2) [3,5,6] profile0_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,9] (choices 2) [3,5,6] profile0_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node23
  · exact profile0_node24
  · exact profile0_node25

def profile0_node26_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 7 26 14 13 21), lower := (rows 7 26 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 12 8 16) }] }

theorem profile0_node26 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,10] 3 profile0_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24,10] 3 profile0_node26_cert).mp (by decide +kernel))

def profile0_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node20 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24] 3 (by decide) (choices 2) [3,9,10] profile0_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6,24] (choices 2) [3,9,10] profile0_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node21
  · exact profile0_node22
  · exact profile0_node26

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile0_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [6] (choices 2) [5,9,12,17,20,24] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node14
  · exact profile0_node15
  · exact profile0_node19
  · exact profile0_node20

def profile0_node29_cert : CutBound 5 := { lost := (rows 0 8 0 1 0), upper := (rows 19 7 13 14 30), lower := (rows 19 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 12 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 19 7 7 0 16) }] }

theorem profile0_node29 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,9] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,9] 3 profile0_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,9] 3 profile0_node29_cert).mp (by decide +kernel))

def profile0_node31_cert : CutBound 5 := { lost := (rows 4 0 0 2 0), upper := (rows 19 7 14 13 24), lower := (rows 19 7 14 13 16), losses := [{ target := 1, region := (rows 1 0 4 10 31), good := (rows 25 29 28 29 16) },{ target := 2, region := (rows 7 2 0 8 28), good := (rows 19 19 27 25 16) }] }

theorem profile0_node31 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10,5] 3 profile0_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10,5] 3 profile0_node31_cert).mp (by decide +kernel))

def profile0_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node30 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10] 3 (by decide) (choices 2) [5] profile0_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5,10] (choices 2) [5] profile0_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node31

def profile0_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node28 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5] 3 (by decide) (choices 2) [9,10] profile0_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,5] (choices 2) [9,10] profile0_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node29
  · exact profile0_node30

def profile0_node33_cert : CutBound 5 := { lost := (rows 0 0 8 2 0), upper := (rows 19 14 7 13 29), lower := (rows 19 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 17 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) }] }

theorem profile0_node33 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,3] 3 profile0_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,3] 3 profile0_node33_cert).mp (by decide +kernel))

def profile0_node34_cert : CutBound 5 := { lost := (rows 8 1 0 0 0), upper := (rows 19 14 13 15 23), lower := (rows 19 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 18 14 14 8 16) },{ target := 3, region := (rows 3 2 4 0 18), good := (rows 19 23 5 0 16) }] }

theorem profile0_node34 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,9] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,9] 3 profile0_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,9] 3 profile0_node34_cert).mp (by decide +kernel))

def profile0_node35_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 19 14 14 13 21), lower := (rows 19 14 14 8 16), losses := [{ target := 0, region := (rows 0 14 14 8 16), good := (rows 22 14 14 14 16) }] }

theorem profile0_node35 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,10] 3 profile0_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12,10] 3 profile0_node35_cert).mp (by decide +kernel))

def profile0_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node32 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12] 3 (by decide) (choices 2) [3,9,10] profile0_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18,12] (choices 2) [3,9,10] profile0_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node33
  · exact profile0_node34
  · exact profile0_node35

def profile0_node27_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile0_node27 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18] 3 (by decide) (choices 2) [5,12] profile0_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [18] (choices 2) [5,12] profile0_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node28
  · exact profile0_node32

def profile0_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [] 3 (by decide) (choices 2) [6,18] profile0_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [] (choices 2) [6,18] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node27

theorem profile0 : Upper (D (n:=5) [34,34,34,34,17]) (R (n:=5) [34,34,34,34,17]) [] 3 := profile0_node0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 11 23 27 19), lower := (rows 15 11 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile1_node2 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,9] 3 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,9] 3 profile1_node2_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 19 7 24 24), lower := (rows 15 19 7 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile1_node4 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,3] 3 profile1_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,3] 3 profile1_node4_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 19 13 26 18), lower := (rows 15 19 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) }] }

theorem profile1_node5 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,9] 3 profile1_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,9] 3 profile1_node5_cert).mp (by decide +kernel))

def profile1_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 14 25 17), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) }] }

theorem profile1_node6 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,10] 3 profile1_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,10] 3 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 19 21 10 26), lower := (rows 15 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile1_node7 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,17] 3 profile1_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,17] 3 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 22 9 25), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile1_node8 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,18] 3 profile1_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,18] 3 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 19 28 11 19), lower := (rows 15 19 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 19 20 0 16) }] }

theorem profile1_node9 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,24] 3 profile1_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17,24] 3 profile1_node9_cert).mp (by decide +kernel))

def profile1_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node3 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile1_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,17] (choices 2) [3,9,10,17,18,24] profile1_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node4
  · exact profile1_node5
  · exact profile1_node6
  · exact profile1_node7
  · exact profile1_node8
  · exact profile1_node9

def profile1_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 26 23 27 19), lower := (rows 15 26 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 18 4 0 16) }] }

theorem profile1_node10 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,24] 3 profile1_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14,24] 3 profile1_node10_cert).mp (by decide +kernel))

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14] 3 (by decide) (choices 2) [9,17,24] profile1_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [14] (choices 2) [9,17,24] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node10

def profile1_node13_cert : CutBound 5 := { lost := (rows 0 8 8 0 0), upper := (rows 27 7 7 24 24), lower := (rows 27 7 7 8 16), losses := [{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile1_node13 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,3] 3 profile1_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,3] 3 profile1_node13_cert).mp (by decide +kernel))

def profile1_node14_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 7 13 26 18), lower := (rows 27 7 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) }] }

theorem profile1_node14 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,9] 3 profile1_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,9] 3 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 7 14 25 17), lower := (rows 27 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 14 8 16) }] }

theorem profile1_node15 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,10] 3 profile1_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,10] 3 profile1_node15_cert).mp (by decide +kernel))

def profile1_node16_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 7 28 11 19), lower := (rows 27 7 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 28 8 16) }] }

theorem profile1_node16 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,24] 3 profile1_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5,24] 3 profile1_node16_cert).mp (by decide +kernel))

def profile1_node12_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile1_node12 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5] 3 (by decide) (choices 2) [3,9,10,24] profile1_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,5] (choices 2) [3,9,10,24] profile1_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node13
  · exact profile1_node14
  · exact profile1_node15
  · exact profile1_node16

def profile1_node17_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 11 23 31 23), lower := (rows 27 11 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile1_node17 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,9] 3 profile1_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,9] 3 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 14 23 27 19), lower := (rows 27 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile1_node18 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,12] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,12] 3 profile1_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,12] 3 profile1_node18_cert).mp (by decide +kernel))

def profile1_node19_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 27 26 7 15 23), lower := (rows 27 26 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 26 26 4 8 16) }] }

theorem profile1_node19 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,24] 3 profile1_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26,24] 3 profile1_node19_cert).mp (by decide +kernel))

def profile1_node11_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile1_node11 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26] 3 (by decide) (choices 2) [5,9,12,24] profile1_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [26] (choices 2) [5,9,12,24] profile1_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node12
  · exact profile1_node17
  · exact profile1_node18
  · exact profile1_node19

def profile1_node21_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 11 23 27 19), lower := (rows 29 11 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile1_node21 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,9] 3 profile1_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,9] 3 profile1_node21_cert).mp (by decide +kernel))

def profile1_node22_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 26 7 11 19), lower := (rows 29 26 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 26 4 8 16) }] }

theorem profile1_node22 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,24] 3 profile1_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28,24] 3 profile1_node22_cert).mp (by decide +kernel))

def profile1_node20_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile1_node20 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28] 3 (by decide) (choices 2) [9,24] profile1_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [28] (choices 2) [9,24] profile1_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node21
  · exact profile1_node22

def profile1_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [] 3 (by decide) (choices 3) [14,26,28] profile1_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [] (choices 3) [14,26,28] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node11
  · exact profile1_node20

theorem profile1 : Upper (D (n:=5) [50,34,33,18,18]) (R (n:=5) [50,34,33,18,18]) [] 3 := profile1_node0

def profile2_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 7 30 26 26), lower := (rows 15 7 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile2_node2 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,5] 3 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,5] 3 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 15 11 22 30 22), lower := (rows 15 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 11 11 0 8 16) }] }

theorem profile2_node3 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,9] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,9] 3 profile2_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,9] 3 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile2_node4 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,12] 3 profile2_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,12] 3 profile2_node4_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 19 14 28 20), lower := (rows 15 19 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 21), good := (rows 23 19 22 0 16) }] }

theorem profile2_node6 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,10] 3 profile2_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,10] 3 profile2_node6_cert).mp (by decide +kernel))

def profile2_node7_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 19 22 12 28), lower := (rows 15 19 22 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) }] }

theorem profile2_node7 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,18] 3 profile2_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,18] 3 profile2_node7_cert).mp (by decide +kernel))

def profile2_node8_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 19 28 14 22), lower := (rows 15 19 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 20 0 16) }] }

theorem profile2_node8 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,24] 3 profile2_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17,24] 3 profile2_node8_cert).mp (by decide +kernel))

def profile2_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node5 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17] 3 (by decide) (choices 2) [10,18,24] profile2_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,17] (choices 2) [10,18,24] profile2_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node6
  · exact profile2_node7
  · exact profile2_node8

def profile2_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 22 7 24 24), lower := (rows 15 22 7 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile2_node10 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,3] 3 profile2_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,3] 3 profile2_node10_cert).mp (by decide +kernel))

def profile2_node11_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 22 13 26 18), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) }] }

theorem profile2_node11 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,9] 3 profile2_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,9] 3 profile2_node11_cert).mp (by decide +kernel))

def profile2_node12_cert : Bound 5 := { allowed := (rows 16 8 16 0 0), upper := (rows 15 22 14 25 17), lower := (rows 15 22 14 8 16), losses := [] }

theorem profile2_node12 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,10] 3 :=
  bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,10] 3 profile2_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,10] 3 profile2_node12_cert).mp (by decide +kernel))

def profile2_node13_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 22 21 10 26), lower := (rows 15 22 21 8 16), losses := [{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) }] }

theorem profile2_node13 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,17] 3 profile2_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,17] 3 profile2_node13_cert).mp (by decide +kernel))

def profile2_node14_cert : Bound 5 := { allowed := (rows 16 8 8 0 0), upper := (rows 15 22 22 9 25), lower := (rows 15 22 22 8 16), losses := [] }

theorem profile2_node14 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,18] 3 :=
  bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,18] 3 profile2_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,18] 3 profile2_node14_cert).mp (by decide +kernel))

def profile2_node15_cert : Bound 5 := { allowed := (rows 16 8 2 0 0), upper := (rows 15 22 28 11 19), lower := (rows 15 22 28 8 16), losses := [] }

theorem profile2_node15 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,24] 3 :=
  bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,24] 3 profile2_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20,24] 3 profile2_node15_cert).mp (by decide +kernel))

def profile2_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node9 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile2_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,20] (choices 2) [3,9,10,17,18,24] profile2_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node10
  · exact profile2_node11
  · exact profile2_node12
  · exact profile2_node13
  · exact profile2_node14
  · exact profile2_node15

def profile2_node16_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 26 23 31 23), lower := (rows 15 26 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 18 4 0 16) }] }

theorem profile2_node16 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,24] 3 profile2_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14,24] 3 profile2_node16_cert).mp (by decide +kernel))

def profile2_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile2_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [14] (choices 2) [5,9,12,17,20,24] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node5
  · exact profile2_node9
  · exact profile2_node16

def profile2_node19_cert : CutBound 5 := { lost := (rows 0 16 16 0 0), upper := (rows 27 7 14 28 20), lower := (rows 27 7 14 8 16), losses := [{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile2_node19 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,10] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,10] 3 profile2_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,10] 3 profile2_node19_cert).mp (by decide +kernel))

def profile2_node20_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 7 28 14 22), lower := (rows 27 7 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 28 8 16) }] }

theorem profile2_node20 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,24] 3 profile2_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5,24] 3 profile2_node20_cert).mp (by decide +kernel))

def profile2_node18_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node18 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5] 3 (by decide) (choices 2) [10,24] profile2_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,5] (choices 2) [10,24] profile2_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node19
  · exact profile2_node20

def profile2_node21_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 27 11 22 30 22), lower := (rows 27 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) }] }

theorem profile2_node21 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,9] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,9] 3 profile2_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,9] 3 profile2_node21_cert).mp (by decide +kernel))

def profile2_node22_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 14 23 31 23), lower := (rows 27 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile2_node22 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,12] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,12] 3 profile2_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,12] 3 profile2_node22_cert).mp (by decide +kernel))

def profile2_node23_cert : CutBound 5 := { lost := (rows 4 4 0 0 0), upper := (rows 27 26 7 15 23), lower := (rows 27 26 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile2_node23 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,24] 3 profile2_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26,24] 3 profile2_node23_cert).mp (by decide +kernel))

def profile2_node17_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node17 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26] 3 (by decide) (choices 2) [5,9,12,24] profile2_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [26] (choices 2) [5,9,12,24] profile2_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node18
  · exact profile2_node21
  · exact profile2_node22
  · exact profile2_node23

def profile2_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [] 3 (by decide) (choices 3) [14,26] profile2_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [] (choices 3) [14,26] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node1
  · exact profile2_node17

theorem profile2 : Upper (D (n:=5) [49,34,34,18,18]) (R (n:=5) [49,34,34,18,18]) [] 3 := profile2_node0

def profile3_node4_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 7 11 21 25 18), lower := (rows 7 11 21 25 16), losses := [{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 13 29 29 16) }] }

theorem profile3_node4 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,17] 3 profile3_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,17] 3 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 7 11 21 26 17), lower := (rows 7 11 21 26 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 21 29 21 28 16) }] }

theorem profile3_node5 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,18] 3 profile3_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17,18] 3 profile3_node5_cert).mp (by decide +kernel))

def profile3_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17] 3 (by decide) (choices 2) [17,18] profile3_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,17] (choices 2) [17,18] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node4
  · exact profile3_node5

def profile3_node6_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 11 22 25 17), lower := (rows 7 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 25 28 8 16) }] }

theorem profile3_node6 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,18] 3 profile3_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9,18] 3 profile3_node6_cert).mp (by decide +kernel))

def profile3_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node2 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9] 3 (by decide) (choices 2) [17,18] profile3_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,9] (choices 2) [17,18] profile3_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node3
  · exact profile3_node6

def profile3_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 19 7 25 25), lower := (rows 7 19 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile3_node8 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,3] 3 profile3_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,3] 3 profile3_node8_cert).mp (by decide +kernel))

def profile3_node10_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 7 19 13 25 18), lower := (rows 7 19 13 25 16), losses := [{ target := 1, region := (rows 1 0 15 10 16), good := (rows 13 29 13 29 16) }] }

theorem profile3_node10 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,17] 3 profile3_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,17] 3 profile3_node10_cert).mp (by decide +kernel))

def profile3_node11_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 19 13 26 17), lower := (rows 7 19 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 26 12 26 16) }] }

theorem profile3_node11 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,18] 3 profile3_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9,18] 3 profile3_node11_cert).mp (by decide +kernel))

def profile3_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node9 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9] 3 (by decide) (choices 2) [17,18] profile3_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,9] (choices 2) [17,18] profile3_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node10
  · exact profile3_node11

def profile3_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 19 14 25 17), lower := (rows 7 19 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 25 28 8 16) }] }

theorem profile3_node12 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,10] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,10] 3 profile3_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,10] 3 profile3_node12_cert).mp (by decide +kernel))

def profile3_node13_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 7 19 21 11 27), lower := (rows 7 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 21 21 8 16) }] }

theorem profile3_node13 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,17] 3 profile3_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,17] 3 profile3_node13_cert).mp (by decide +kernel))

def profile3_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 19 22 9 25), lower := (rows 7 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 22 22 8 16) }] }

theorem profile3_node14 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,18] 3 profile3_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,18] 3 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 7 19 28 11 19), lower := (rows 7 19 28 8 16), losses := [{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 11 12 8 0) }] }

theorem profile3_node15 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,24] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,24] 3 profile3_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17,24] 3 profile3_node15_cert).mp (by decide +kernel))

def profile3_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node7 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile3_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,17] (choices 2) [3,9,10,17,18,24] profile3_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node8
  · exact profile3_node9
  · exact profile3_node12
  · exact profile3_node13
  · exact profile3_node14
  · exact profile3_node15

def profile3_node17_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 26 7 25 17), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) }] }

theorem profile3_node17 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,3] 3 profile3_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,3] 3 profile3_node17_cert).mp (by decide +kernel))

def profile3_node18_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 7 26 21 11 19), lower := (rows 7 26 21 8 16), losses := [{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 10 13 8 0) }] }

theorem profile3_node18 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,17] 3 profile3_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24,17] 3 profile3_node18_cert).mp (by decide +kernel))

def profile3_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node16 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24] 3 (by decide) (choices 2) [3,17] profile3_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6,24] (choices 2) [3,17] profile3_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node17
  · exact profile3_node18

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6] 3 (by decide) (choices 2) [9,17,24] profile3_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [6] (choices 2) [9,17,24] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node7
  · exact profile3_node16

def profile3_node21_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 13 19 7 27 19), lower := (rows 13 19 7 8 16), losses := [{ target := 4, region := (rows 1 2 6 8 0), good := (rows 13 7 7 8 0) }] }

theorem profile3_node21 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,3] 3 profile3_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,3] 3 profile3_node21_cert).mp (by decide +kernel))

def profile3_node22_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 13 19 21 11 19), lower := (rows 13 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile3_node22 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,17] 3 profile3_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,17] 3 profile3_node22_cert).mp (by decide +kernel))

def profile3_node23_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 13 19 22 11 19), lower := (rows 13 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 12 22 22 8 16) }] }

theorem profile3_node23 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,18] 3 profile3_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17,18] 3 profile3_node23_cert).mp (by decide +kernel))

def profile3_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node20 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17] 3 (by decide) (choices 2) [3,17,18] profile3_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12,17] (choices 2) [3,17,18] profile3_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node21
  · exact profile3_node22
  · exact profile3_node23

def profile3_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node19 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12] 3 (by decide) (choices 2) [17] profile3_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [12] (choices 2) [17] profile3_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node20

def profile3_node26_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 19 7 7 25 25), lower := (rows 19 7 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile3_node26 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,3] 3 profile3_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,3] 3 profile3_node26_cert).mp (by decide +kernel))

def profile3_node27_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 19 7 13 27 19), lower := (rows 19 7 13 8 16), losses := [{ target := 4, region := (rows 1 6 4 8 0), good := (rows 3 7 15 8 0) }] }

theorem profile3_node27 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,9] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,9] 3 profile3_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,9] 3 profile3_node27_cert).mp (by decide +kernel))

def profile3_node28_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 19 7 14 25 17), lower := (rows 19 7 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 25 29 28 8 16) }] }

theorem profile3_node28 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,10] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,10] 3 profile3_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,10] 3 profile3_node28_cert).mp (by decide +kernel))

def profile3_node29_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 19 7 21 11 27), lower := (rows 19 7 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 5 21 8 16) }] }

theorem profile3_node29 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,17] 3 profile3_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,17] 3 profile3_node29_cert).mp (by decide +kernel))

def profile3_node30_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 7 22 9 25), lower := (rows 19 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 6 22 8 16) }] }

theorem profile3_node30 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,18] 3 profile3_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,18] 3 profile3_node30_cert).mp (by decide +kernel))

def profile3_node31_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 19 7 28 11 19), lower := (rows 19 7 28 8 16), losses := [{ target := 4, region := (rows 1 2 4 11 0), good := (rows 11 15 12 8 0) }] }

theorem profile3_node31 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,24] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,24] 3 profile3_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5,24] 3 profile3_node31_cert).mp (by decide +kernel))

def profile3_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node25 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile3_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,5] (choices 2) [3,9,10,17,18,24] profile3_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node26
  · exact profile3_node27
  · exact profile3_node28
  · exact profile3_node29
  · exact profile3_node30
  · exact profile3_node31

def profile3_node33_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 19 14 7 25 17), lower := (rows 19 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile3_node33 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,3] 3 profile3_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,3] 3 profile3_node33_cert).mp (by decide +kernel))

def profile3_node34_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 19 14 21 11 19), lower := (rows 19 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) }] }

theorem profile3_node34 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,17] 3 profile3_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12,17] 3 profile3_node34_cert).mp (by decide +kernel))

def profile3_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node32 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12] 3 (by decide) (choices 2) [3,17] profile3_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,12] (choices 2) [3,17] profile3_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node33
  · exact profile3_node34

def profile3_node35_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 19 19 15 15 31), lower := (rows 19 19 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile3_node35 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,17] 3 profile3_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,17] 3 profile3_node35_cert).mp (by decide +kernel))

def profile3_node36_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 19 22 15 11 27), lower := (rows 19 22 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile3_node36 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,20] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,20] 3 profile3_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18,20] 3 profile3_node36_cert).mp (by decide +kernel))

def profile3_node24_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile3_node24 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18] 3 (by decide) (choices 2) [5,12,17,20] profile3_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [18] (choices 2) [5,12,17,20] profile3_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node25
  · exact profile3_node32
  · exact profile3_node35
  · exact profile3_node36

def profile3_node39_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 21 11 7 27 19), lower := (rows 21 11 7 8 16), losses := [{ target := 4, region := (rows 1 2 6 8 0), good := (rows 5 15 7 8 0) }] }

theorem profile3_node39 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,3] 3 profile3_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,3] 3 profile3_node39_cert).mp (by decide +kernel))

def profile3_node40_cert : CutBound 5 := { lost := (rows 2 0 2 0 0), upper := (rows 21 11 21 11 19), lower := (rows 21 11 21 8 16), losses := [{ target := 1, region := (rows 21 0 21 8 16), good := (rows 21 13 21 8 21) }] }

theorem profile3_node40 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,17] 3 profile3_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,17] 3 profile3_node40_cert).mp (by decide +kernel))

def profile3_node41_cert : CutBound 5 := { lost := (rows 2 0 0 0 0), upper := (rows 21 11 22 11 19), lower := (rows 21 11 22 8 16), losses := [{ target := 1, region := (rows 5 0 4 8 16), good := (rows 21 9 21 8 16) }] }

theorem profile3_node41 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,18] 3 profile3_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9,18] 3 profile3_node41_cert).mp (by decide +kernel))

def profile3_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node38 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9] 3 (by decide) (choices 2) [3,17,18] profile3_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,9] (choices 2) [3,17,18] profile3_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node39
  · exact profile3_node40
  · exact profile3_node41

def profile3_node42_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 21 19 15 11 27), lower := (rows 21 19 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 5 15 4 8 0) }] }

theorem profile3_node42 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,17] 3 profile3_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,17] 3 profile3_node42_cert).mp (by decide +kernel))

def profile3_node44_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 21 26 7 11 19), lower := (rows 21 26 7 8 16), losses := [{ target := 4, region := (rows 1 2 4 12 0), good := (rows 13 10 15 8 0) }] }

theorem profile3_node44 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24,3] 3 profile3_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24,3] 3 profile3_node44_cert).mp (by decide +kernel))

def profile3_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node43 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24] 3 (by decide) (choices 2) [3] profile3_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20,24] (choices 2) [3] profile3_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node44

def profile3_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node37 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20] 3 (by decide) (choices 2) [9,17,24] profile3_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [20] (choices 2) [9,17,24] profile3_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node38
  · exact profile3_node42
  · exact profile3_node43

def profile3_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [] 3 (by decide) (choices 2) [6,12,18,20] profile3_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [] (choices 2) [6,12,18,20] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node19
  · exact profile3_node24
  · exact profile3_node37

theorem profile3 : Upper (D (n:=5) [35,34,33,33,18]) (R (n:=5) [35,34,33,33,18]) [] 3 := profile3_node0

#print axioms profile3
end Delivery.FiveVertexPositive09
