import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile6_node3_cert : CutBound 5 := { lost := (rows 0 24 0 5 0), upper := (rows 15 7 21 26 26), lower := (rows 15 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 7 7 23 0 16) },{ target := 4, region := (rows 1 7 4 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile6_node3 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,17] 3 profile6_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,17] 3 profile6_node3_cert).mp (by decide +kernel))

def profile6_node4_cert : CutBound 5 := { lost := (rows 0 24 0 6 0), upper := (rows 15 7 22 25 25), lower := (rows 15 7 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 22 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 6 8 0) }] }

theorem profile6_node4 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,18] 3 profile6_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,18] 3 profile6_node4_cert).mp (by decide +kernel))

def profile6_node5_cert : CutBound 5 := { lost := (rows 16 24 0 4 0), upper := (rows 15 7 28 27 19), lower := (rows 15 7 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 5 7 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile6_node5 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,24] 3 profile6_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5,24] 3 profile6_node5_cert).mp (by decide +kernel))

def profile6_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node2 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] 3 (by decide) (choices 2) [17,18,24] profile6_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] (choices 2) [17,18,24] profile6_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node3
  · exact profile6_node4
  · exact profile6_node5

def profile6_node6_cert : CutBound 5 := { lost := (rows 16 17 8 4 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node6 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 3 profile6_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 3 profile6_node6_cert).mp (by decide +kernel))

def profile6_node8_cert : CutBound 5 := { lost := (rows 0 0 24 3 0), upper := (rows 15 19 7 28 28), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile6_node8 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 3 profile6_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 3 profile6_node8_cert).mp (by decide +kernel))

def profile6_node9_cert : CutBound 5 := { lost := (rows 0 8 18 1 0), upper := (rows 15 19 13 30 22), lower := (rows 15 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile6_node9 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 3 profile6_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 3 profile6_node9_cert).mp (by decide +kernel))

def profile6_node10_cert : CutBound 5 := { lost := (rows 16 8 17 2 0), upper := (rows 15 19 14 29 21), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile6_node10 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 3 profile6_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 3 profile6_node10_cert).mp (by decide +kernel))

def profile6_node11_cert : CutBound 5 := { lost := (rows 0 12 10 1 0), upper := (rows 15 19 21 14 30), lower := (rows 15 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 19 19 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile6_node11 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 3 profile6_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 3 profile6_node11_cert).mp (by decide +kernel))

def profile6_node12_cert : CutBound 5 := { lost := (rows 16 0 9 18 0), upper := (rows 15 19 22 13 29), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile6_node12 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 3 profile6_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 3 profile6_node12_cert).mp (by decide +kernel))

def profile6_node14_cert : CutBound 5 := { lost := (rows 0 8 3 4 0), upper := (rows 15 19 28 11 20), lower := (rows 15 19 28 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 31), good := (rows 30 22 28 30 16) },{ target := 1, region := (rows 1 0 13 8 31), good := (rows 29 21 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) },{ target := 3, region := (rows 1 11 4 0 21), good := (rows 23 19 22 19 16) }] }

theorem profile6_node14 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,3] 3 profile6_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,3] 3 profile6_node14_cert).mp (by decide +kernel))

def profile6_node15_cert : CutBound 5 := { lost := (rows 0 4 3 2 0), upper := (rows 15 19 28 13 18), lower := (rows 15 19 28 13 16), losses := [{ target := 0, region := (rows 0 2 13 8 19), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) },{ target := 2, region := (rows 1 11 0 8 31), good := (rows 27 19 26 27 16) }] }

theorem profile6_node15 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,5] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,5] 3 profile6_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,5] 3 profile6_node15_cert).mp (by decide +kernel))

def profile6_node16_cert : CutBound 5 := { lost := (rows 0 4 3 1 0), upper := (rows 15 19 28 14 17), lower := (rows 15 19 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) },{ target := 1, region := (rows 1 0 13 8 19), good := (rows 29 21 28 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 19 24 26 16) }] }

theorem profile6_node16 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,6] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,6] 3 profile6_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24,6] 3 profile6_node16_cert).mp (by decide +kernel))

def profile6_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node13 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] 3 (by decide) (choices 2) [3,5,6] profile6_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] (choices 2) [3,5,6] profile6_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node14
  · exact profile6_node15
  · exact profile6_node16

def profile6_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node7 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile6_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17] (choices 2) [3,9,10,17,18,24] profile6_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node10
  · exact profile6_node11
  · exact profile6_node12
  · exact profile6_node13

def profile6_node18_cert : CutBound 5 := { lost := (rows 0 0 24 6 0), upper := (rows 15 22 7 25 25), lower := (rows 15 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 7 8 0) }] }

theorem profile6_node18 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,3] 3 profile6_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,3] 3 profile6_node18_cert).mp (by decide +kernel))

def profile6_node19_cert : CutBound 5 := { lost := (rows 0 8 18 4 0), upper := (rows 15 22 13 27 19), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 13 8 0) }] }

theorem profile6_node19 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,9] 3 profile6_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,9] 3 profile6_node19_cert).mp (by decide +kernel))

def profile6_node20_cert : CutBound 5 := { lost := (rows 0 8 1 6 0), upper := (rows 15 22 14 25 17), lower := (rows 15 22 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 20 12 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile6_node20 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,10] 3 profile6_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,10] 3 profile6_node20_cert).mp (by decide +kernel))

def profile6_node21_cert : CutBound 5 := { lost := (rows 16 9 0 20 0), upper := (rows 15 22 21 11 27), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile6_node21 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,17] 3 profile6_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,17] 3 profile6_node21_cert).mp (by decide +kernel))

def profile6_node22_cert : CutBound 5 := { lost := (rows 0 1 1 6 0), upper := (rows 15 22 22 9 25), lower := (rows 15 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 20 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 18 8 16) }] }

theorem profile6_node22 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,18] 3 profile6_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,18] 3 profile6_node22_cert).mp (by decide +kernel))

def profile6_node23_cert : CutBound 5 := { lost := (rows 16 9 0 20 0), upper := (rows 15 22 28 11 19), lower := (rows 15 22 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 24 8 16) },{ target := 3, region := (rows 1 7 4 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile6_node23 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,24] 3 profile6_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20,24] 3 profile6_node23_cert).mp (by decide +kernel))

def profile6_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node17 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile6_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] (choices 2) [3,9,10,17,18,24] profile6_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node18
  · exact profile6_node19
  · exact profile6_node20
  · exact profile6_node21
  · exact profile6_node22
  · exact profile6_node23

def profile6_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile6_node1 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile6_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14] (choices 2) [5,12,17,20] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node2
  · exact profile6_node6
  · exact profile6_node7
  · exact profile6_node17

def profile6_node26_cert : CutBound 5 := { lost := (rows 0 24 0 5 0), upper := (rows 23 7 13 26 26), lower := (rows 23 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 7 4 8 0), good := (rows 7 7 15 8 0) }] }

theorem profile6_node26 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,9] 3 profile6_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,9] 3 profile6_node26_cert).mp (by decide +kernel))

def profile6_node27_cert : CutBound 5 := { lost := (rows 0 24 0 6 0), upper := (rows 23 7 14 25 25), lower := (rows 23 7 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 6 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 7 7 14 8 0) }] }

theorem profile6_node27 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,10] 3 profile6_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,10] 3 profile6_node27_cert).mp (by decide +kernel))

def profile6_node28_cert : CutBound 5 := { lost := (rows 8 24 0 20 0), upper := (rows 23 7 28 11 27), lower := (rows 23 7 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 5 7 4 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile6_node28 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,24] 3 profile6_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5,24] 3 profile6_node28_cert).mp (by decide +kernel))

def profile6_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node25 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] 3 (by decide) (choices 2) [9,10,24] profile6_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] (choices 2) [9,10,24] profile6_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node26
  · exact profile6_node27
  · exact profile6_node28

def profile6_node30_cert : CutBound 5 := { lost := (rows 0 0 24 3 0), upper := (rows 23 11 7 28 28), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile6_node30 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 3 profile6_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 3 profile6_node30_cert).mp (by decide +kernel))

def profile6_node31_cert : CutBound 5 := { lost := (rows 0 20 18 1 0), upper := (rows 23 11 13 30 22), lower := (rows 23 11 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 11 11 8 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile6_node31 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 3 profile6_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 3 profile6_node31_cert).mp (by decide +kernel))

def profile6_node32_cert : CutBound 5 := { lost := (rows 8 0 17 2 0), upper := (rows 23 11 14 29 21), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 14 8 0) }] }

theorem profile6_node32 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 3 profile6_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 3 profile6_node32_cert).mp (by decide +kernel))

def profile6_node33_cert : CutBound 5 := { lost := (rows 0 16 10 17 0), upper := (rows 23 11 21 14 30), lower := (rows 23 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 7 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile6_node33 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 3 profile6_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 3 profile6_node33_cert).mp (by decide +kernel))

def profile6_node34_cert : CutBound 5 := { lost := (rows 8 0 9 2 0), upper := (rows 23 11 22 13 29), lower := (rows 23 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile6_node34 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 3 profile6_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 3 profile6_node34_cert).mp (by decide +kernel))

def profile6_node36_cert : CutBound 5 := { lost := (rows 0 4 3 4 0), upper := (rows 23 11 28 11 20), lower := (rows 23 11 28 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 31), good := (rows 22 30 28 30 16) },{ target := 1, region := (rows 1 0 14 8 31), good := (rows 21 29 28 29 16) },{ target := 2, region := (rows 1 11 0 11 16), good := (rows 27 11 26 11 16) }] }

theorem profile6_node36 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,3] 3 profile6_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,3] 3 profile6_node36_cert).mp (by decide +kernel))

def profile6_node37_cert : CutBound 5 := { lost := (rows 0 4 3 2 0), upper := (rows 23 11 28 13 18), lower := (rows 23 11 28 13 16), losses := [{ target := 0, region := (rows 0 2 14 8 19), good := (rows 22 30 28 28 16) },{ target := 1, region := (rows 1 0 5 11 16), good := (rows 29 13 28 13 16) },{ target := 2, region := (rows 1 10 0 8 31), good := (rows 19 27 26 27 16) }] }

theorem profile6_node37 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,5] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,5] 3 profile6_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,5] 3 profile6_node37_cert).mp (by decide +kernel))

def profile6_node38_cert : CutBound 5 := { lost := (rows 8 0 3 1 0), upper := (rows 23 11 28 14 17), lower := (rows 23 11 28 14 16), losses := [{ target := 0, region := (rows 0 2 5 11 16), good := (rows 30 14 28 14 16) },{ target := 1, region := (rows 1 0 14 8 19), good := (rows 21 29 28 28 16) },{ target := 3, region := (rows 9 2 4 0 31), good := (rows 23 19 21 23 16) }] }

theorem profile6_node38 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,6] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,6] 3 profile6_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24,6] 3 profile6_node38_cert).mp (by decide +kernel))

def profile6_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node35 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] 3 (by decide) (choices 2) [3,5,6] profile6_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] (choices 2) [3,5,6] profile6_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node36
  · exact profile6_node37
  · exact profile6_node38

def profile6_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node29 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile6_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9] (choices 2) [3,9,10,17,18,24] profile6_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node30
  · exact profile6_node31
  · exact profile6_node32
  · exact profile6_node33
  · exact profile6_node34
  · exact profile6_node35

def profile6_node40_cert : CutBound 5 := { lost := (rows 0 0 24 6 0), upper := (rows 23 14 7 25 25), lower := (rows 23 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 7 14 7 8 0) }] }

theorem profile6_node40 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,3] 3 profile6_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,3] 3 profile6_node40_cert).mp (by decide +kernel))

def profile6_node41_cert : CutBound 5 := { lost := (rows 8 17 0 4 0), upper := (rows 23 14 13 27 19), lower := (rows 23 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 14 14 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 7 14 15 8 0) }] }

theorem profile6_node41 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,9] 3 profile6_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,9] 3 profile6_node41_cert).mp (by decide +kernel))

def profile6_node42_cert : CutBound 5 := { lost := (rows 0 1 1 6 0), upper := (rows 23 14 14 25 17), lower := (rows 23 14 14 8 16), losses := [{ target := 0, region := (rows 0 14 14 8 16), good := (rows 22 14 14 14 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 12 12 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 10 8 16) }] }

theorem profile6_node42 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,10] 3 profile6_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,10] 3 profile6_node42_cert).mp (by decide +kernel))

def profile6_node43_cert : CutBound 5 := { lost := (rows 0 16 10 20 0), upper := (rows 23 14 21 11 27), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 21 0 16) },{ target := 4, region := (rows 1 7 4 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile6_node43 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,17] 3 profile6_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,17] 3 profile6_node43_cert).mp (by decide +kernel))

def profile6_node44_cert : CutBound 5 := { lost := (rows 8 0 9 6 0), upper := (rows 23 14 22 9 25), lower := (rows 23 14 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 12 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 18 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile6_node44 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,18] 3 profile6_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,18] 3 profile6_node44_cert).mp (by decide +kernel))

def profile6_node45_cert : CutBound 5 := { lost := (rows 8 17 0 20 0), upper := (rows 23 14 28 11 19), lower := (rows 23 14 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 14 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 24 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 7 4 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile6_node45 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,24] 3 profile6_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12,24] 3 profile6_node45_cert).mp (by decide +kernel))

def profile6_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node39 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile6_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] (choices 2) [3,9,10,17,18,24] profile6_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node40
  · exact profile6_node41
  · exact profile6_node42
  · exact profile6_node43
  · exact profile6_node44
  · exact profile6_node45

def profile6_node46_cert : CutBound 5 := { lost := (rows 0 12 16 16 0), upper := (rows 23 19 15 15 31), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node46 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 3 profile6_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 3 profile6_node46_cert).mp (by decide +kernel))

def profile6_node47_cert : CutBound 5 := { lost := (rows 8 9 0 4 0), upper := (rows 23 22 15 11 27), lower := (rows 23 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 22 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile6_node47 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 3 profile6_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 3 profile6_node47_cert).mp (by decide +kernel))

def profile6_node49_cert : CutBound 5 := { lost := (rows 8 0 24 18 0), upper := (rows 23 26 7 13 29), lower := (rows 23 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 10 15 8 0) }] }

theorem profile6_node49 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,3] 3 profile6_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,3] 3 profile6_node49_cert).mp (by decide +kernel))

def profile6_node51_cert : CutBound 5 := { lost := (rows 0 5 2 4 0), upper := (rows 23 26 13 11 20), lower := (rows 23 26 13 11 16), losses := [{ target := 0, region := (rows 0 14 4 8 21), good := (rows 22 26 30 26 16) },{ target := 1, region := (rows 1 0 12 8 31), good := (rows 21 28 29 29 16) },{ target := 2, region := (rows 1 3 0 13 16), good := (rows 27 26 11 11 16) }] }

theorem profile6_node51 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,3] 3 profile6_node51_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,3] 3 profile6_node51_cert).mp (by decide +kernel))

def profile6_node52_cert : CutBound 5 := { lost := (rows 0 5 2 2 0), upper := (rows 23 26 13 13 18), lower := (rows 23 26 13 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 31), good := (rows 22 26 30 30 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 29 28 13 13 16) },{ target := 2, region := (rows 1 14 0 8 31), good := (rows 19 26 27 27 16) }] }

theorem profile6_node52 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,5] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,5] 3 profile6_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,5] 3 profile6_node52_cert).mp (by decide +kernel))

def profile6_node53_cert : CutBound 5 := { lost := (rows 8 5 0 1 0), upper := (rows 23 26 13 14 17), lower := (rows 23 26 13 14 16), losses := [{ target := 0, region := (rows 0 3 4 13 16), good := (rows 30 26 14 14 16) },{ target := 2, region := (rows 1 14 0 8 21), good := (rows 19 26 27 26 16) },{ target := 3, region := (rows 9 2 4 0 31), good := (rows 23 19 21 23 16) }] }

theorem profile6_node53 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,6] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,6] 3 profile6_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9,6] 3 profile6_node53_cert).mp (by decide +kernel))

def profile6_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node50 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9] 3 (by decide) (choices 2) [3,5,6] profile6_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,9] (choices 2) [3,5,6] profile6_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node51
  · exact profile6_node52
  · exact profile6_node53

def profile6_node54_cert : CutBound 5 := { lost := (rows 8 0 17 18 0), upper := (rows 23 26 14 13 21), lower := (rows 23 26 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 18 23 0 16) },{ target := 4, region := (rows 1 2 7 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile6_node54 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,10] 3 profile6_node54_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24,10] 3 profile6_node54_cert).mp (by decide +kernel))

def profile6_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node48 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] 3 (by decide) (choices 2) [3,9,10] profile6_node48_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] (choices 2) [3,9,10] profile6_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node49
  · exact profile6_node50
  · exact profile6_node54

def profile6_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node24 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile6_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22] (choices 2) [5,9,12,17,20,24] profile6_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node25
  · exact profile6_node29
  · exact profile6_node39
  · exact profile6_node46
  · exact profile6_node47
  · exact profile6_node48

def profile6_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile6_node0 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 3 (by decide) (choices 3) [14,22] profile6_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] (choices 3) [14,22] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node1
  · exact profile6_node24

theorem profile6 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 3 := profile6_node0

def profile7_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 7 30 26 26), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile7_node2 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,5] 3 profile7_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,5] 3 profile7_node2_cert).mp (by decide +kernel))

def profile7_node3_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile7_node3 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,12] 3 profile7_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,12] 3 profile7_node3_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 5 := { lost := (rows 16 8 16 0 0), upper := (rows 15 19 14 30 22), lower := (rows 15 19 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 21), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile7_node5 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,10] 3 profile7_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,10] 3 profile7_node5_cert).mp (by decide +kernel))

def profile7_node6_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 19 22 14 30), lower := (rows 15 19 22 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile7_node6 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,18] 3 profile7_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,18] 3 profile7_node6_cert).mp (by decide +kernel))

def profile7_node7_cert : CutBound 5 := { lost := (rows 0 8 0 16 0), upper := (rows 15 19 28 14 22), lower := (rows 15 19 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 20 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile7_node7 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,24] 3 profile7_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17,24] 3 profile7_node7_cert).mp (by decide +kernel))

def profile7_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node4 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17] 3 (by decide) (choices 2) [10,18,24] profile7_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,17] (choices 2) [10,18,24] profile7_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node5
  · exact profile7_node6
  · exact profile7_node7

def profile7_node9_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 15 22 7 26 26), lower := (rows 15 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile7_node9 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,3] 3 profile7_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,3] 3 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 15 22 13 26 18), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) }] }

theorem profile7_node10 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,9] 3 profile7_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,9] 3 profile7_node10_cert).mp (by decide +kernel))

def profile7_node11_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 22 14 27 19), lower := (rows 15 22 14 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile7_node11 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,10] 3 profile7_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,10] 3 profile7_node11_cert).mp (by decide +kernel))

def profile7_node12_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 22 21 10 26), lower := (rows 15 22 21 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) }] }

theorem profile7_node12 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,17] 3 profile7_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,17] 3 profile7_node12_cert).mp (by decide +kernel))

def profile7_node13_cert : CutBound 5 := { lost := (rows 0 8 8 4 0), upper := (rows 15 22 22 11 27), lower := (rows 15 22 22 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 18 8 16) },{ target := 3, region := (rows 1 22 22 0 16), good := (rows 7 22 22 0 22) }] }

theorem profile7_node13 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,18] 3 profile7_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,18] 3 profile7_node13_cert).mp (by decide +kernel))

def profile7_node14_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 22 28 11 19), lower := (rows 15 22 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 24 8 16) },{ target := 3, region := (rows 1 7 4 0 17), good := (rows 23 22 22 0 16) }] }

theorem profile7_node14 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,24] 3 profile7_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20,24] 3 profile7_node14_cert).mp (by decide +kernel))

def profile7_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node8 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile7_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14,20] (choices 2) [3,9,10,17,18,24] profile7_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node9
  · exact profile7_node10
  · exact profile7_node11
  · exact profile7_node12
  · exact profile7_node13
  · exact profile7_node14

def profile7_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile7_node1 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile7_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [14] (choices 2) [5,12,17,20] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node4
  · exact profile7_node8

def profile7_node16_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 23 7 30 26 26), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile7_node16 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,5] 3 profile7_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,5] 3 profile7_node16_cert).mp (by decide +kernel))

def profile7_node18_cert : CutBound 5 := { lost := (rows 8 0 16 0 0), upper := (rows 23 11 14 30 22), lower := (rows 23 11 14 8 16), losses := [{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 14 8 0) }] }

theorem profile7_node18 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,10] 3 profile7_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,10] 3 profile7_node18_cert).mp (by decide +kernel))

def profile7_node19_cert : CutBound 5 := { lost := (rows 8 0 8 0 0), upper := (rows 23 11 22 14 30), lower := (rows 23 11 22 8 16), losses := [{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile7_node19 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,18] 3 profile7_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,18] 3 profile7_node19_cert).mp (by decide +kernel))

def profile7_node20_cert : CutBound 5 := { lost := (rows 0 16 0 16 0), upper := (rows 23 11 28 14 22), lower := (rows 23 11 28 8 16), losses := [{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile7_node20 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,24] 3 profile7_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9,24] 3 profile7_node20_cert).mp (by decide +kernel))

def profile7_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node17 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9] 3 (by decide) (choices 2) [10,18,24] profile7_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,9] (choices 2) [10,18,24] profile7_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node18
  · exact profile7_node19
  · exact profile7_node20

def profile7_node22_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 23 14 7 26 26), lower := (rows 23 14 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) }] }

theorem profile7_node22 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,3] 3 profile7_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,3] 3 profile7_node22_cert).mp (by decide +kernel))

def profile7_node23_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 14 13 26 18), lower := (rows 23 14 13 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile7_node23 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,9] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,9] 3 profile7_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,9] 3 profile7_node23_cert).mp (by decide +kernel))

def profile7_node24_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 14 14 27 19), lower := (rows 23 14 14 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 10 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile7_node24 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,10] 3 profile7_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,10] 3 profile7_node24_cert).mp (by decide +kernel))

def profile7_node25_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 23 14 21 10 26), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) }] }

theorem profile7_node25 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,17] 3 profile7_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,17] 3 profile7_node25_cert).mp (by decide +kernel))

def profile7_node26_cert : CutBound 5 := { lost := (rows 8 0 8 4 0), upper := (rows 23 14 22 11 27), lower := (rows 23 14 22 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 18 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile7_node26 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,18] 3 profile7_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,18] 3 profile7_node26_cert).mp (by decide +kernel))

def profile7_node27_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 14 28 11 19), lower := (rows 23 14 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 24 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile7_node27 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,24] 3 profile7_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12,24] 3 profile7_node27_cert).mp (by decide +kernel))

def profile7_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node21 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile7_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,12] (choices 2) [3,9,10,17,18,24] profile7_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node22
  · exact profile7_node23
  · exact profile7_node24
  · exact profile7_node25
  · exact profile7_node26
  · exact profile7_node27

def profile7_node28_cert : CutBound 5 := { lost := (rows 0 12 0 0 0), upper := (rows 23 19 14 14 30), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) }] }

theorem profile7_node28 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,17] 3 profile7_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,17] 3 profile7_node28_cert).mp (by decide +kernel))

def profile7_node29_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 22 15 11 27), lower := (rows 23 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile7_node29 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,20] 3 profile7_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,20] 3 profile7_node29_cert).mp (by decide +kernel))

def profile7_node30_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 26 15 15 31), lower := (rows 23 26 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile7_node30 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,24] 3 profile7_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22,24] 3 profile7_node30_cert).mp (by decide +kernel))

def profile7_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node15 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile7_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [22] (choices 2) [5,9,12,17,20,24] profile7_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node16
  · exact profile7_node17
  · exact profile7_node21
  · exact profile7_node28
  · exact profile7_node29
  · exact profile7_node30

def profile7_node32_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 29 7 30 26 26), lower := (rows 29 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile7_node32 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,5] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,5] 3 profile7_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,5] 3 profile7_node32_cert).mp (by decide +kernel))

def profile7_node34_cert : CutBound 5 := { lost := (rows 0 16 16 4 0), upper := (rows 29 14 7 26 18), lower := (rows 29 14 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 26 27 8 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile7_node34 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,3] 3 profile7_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,3] 3 profile7_node34_cert).mp (by decide +kernel))

def profile7_node35_cert : CutBound 5 := { lost := (rows 0 16 0 16 0), upper := (rows 29 14 22 11 19), lower := (rows 29 14 22 8 16), losses := [{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 14 6 8 0) }] }

theorem profile7_node35 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,18] 3 profile7_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12,18] 3 profile7_node35_cert).mp (by decide +kernel))

def profile7_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node33 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12] 3 (by decide) (choices 2) [3,18] profile7_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,12] (choices 2) [3,18] profile7_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node34
  · exact profile7_node35

def profile7_node36_cert : CutBound 5 := { lost := (rows 0 12 0 0 0), upper := (rows 29 19 14 14 30), lower := (rows 29 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) }] }

theorem profile7_node36 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,17] 3 profile7_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,17] 3 profile7_node36_cert).mp (by decide +kernel))

def profile7_node38_cert : CutBound 5 := { lost := (rows 0 8 8 4 0), upper := (rows 29 22 7 10 26), lower := (rows 29 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 26 27 8 16) },{ target := 3, region := (rows 1 3 5 0 16), good := (rows 23 22 7 0 16) }] }

theorem profile7_node38 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,3] 3 profile7_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,3] 3 profile7_node38_cert).mp (by decide +kernel))

def profile7_node40_cert : CutBound 5 := { lost := (rows 0 8 16 0 0), upper := (rows 29 22 14 11 18), lower := (rows 29 22 14 11 16), losses := [{ target := 3, region := (rows 1 7 4 0 31), good := (rows 23 22 22 19 16) },{ target := 4, region := (rows 1 2 12 8 0), good := (rows 13 6 14 15 0) }] }

theorem profile7_node40 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10,3] 3 profile7_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10,3] 3 profile7_node40_cert).mp (by decide +kernel))

def profile7_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node39 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10] 3 (by decide) (choices 2) [3] profile7_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20,10] (choices 2) [3] profile7_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node40

def profile7_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node37 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20] 3 (by decide) (choices 2) [3,10] profile7_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28,20] (choices 2) [3,10] profile7_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile7_node38
  · exact profile7_node39

def profile7_node31_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile7_node31 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28] 3 (by decide) (choices 2) [5,12,17,20] profile7_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [28] (choices 2) [5,12,17,20] profile7_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node32
  · exact profile7_node33
  · exact profile7_node36
  · exact profile7_node37

def profile7_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile7_node0 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [] 3 (by decide) (choices 3) [14,22,28] profile7_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [] (choices 3) [14,22,28] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node1
  · exact profile7_node15
  · exact profile7_node31

theorem profile7 : Upper (D (n:=5) [49,35,34,34,18]) (R (n:=5) [49,35,34,34,18]) [] 3 := profile7_node0

def profile8_node3_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 15 19 21 30 22), lower := (rows 15 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile8_node3 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,17] 3 profile8_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,17] 3 profile8_node3_cert).mp (by decide +kernel))

def profile8_node4_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 15 19 22 29 21), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile8_node4 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,18] 3 profile8_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17,18] 3 profile8_node4_cert).mp (by decide +kernel))

def profile8_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node2 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17] 3 (by decide) (choices 2) [17,18] profile8_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,17] (choices 2) [17,18] profile8_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node3
  · exact profile8_node4

def profile8_node6_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 15 22 21 27 19), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) }] }

theorem profile8_node6 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,17] 3 profile8_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,17] 3 profile8_node6_cert).mp (by decide +kernel))

def profile8_node7_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 15 22 22 25 17), lower := (rows 15 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) }] }

theorem profile8_node7 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,18] 3 profile8_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20,18] 3 profile8_node7_cert).mp (by decide +kernel))

def profile8_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node5 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20] 3 (by decide) (choices 2) [17,18] profile8_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14,20] (choices 2) [17,18] profile8_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node6
  · exact profile8_node7

def profile8_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14] 3 (by decide) (choices 2) [17,20] profile8_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [14] (choices 2) [17,20] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node2
  · exact profile8_node5

def profile8_node9_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 23 7 31 27 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 7 7 4 8 0) }] }

theorem profile8_node9 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,5] 3 profile8_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,5] 3 profile8_node9_cert).mp (by decide +kernel))

def profile8_node11_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 23 11 21 30 22), lower := (rows 23 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) }] }

theorem profile8_node11 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,17] 3 profile8_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,17] 3 profile8_node11_cert).mp (by decide +kernel))

def profile8_node12_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 11 22 29 21), lower := (rows 23 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile8_node12 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,18] 3 profile8_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9,18] 3 profile8_node12_cert).mp (by decide +kernel))

def profile8_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node10 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9] 3 (by decide) (choices 2) [17,18] profile8_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,9] (choices 2) [17,18] profile8_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node11
  · exact profile8_node12

def profile8_node14_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 23 14 21 27 19), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) }] }

theorem profile8_node14 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,17] 3 profile8_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,17] 3 profile8_node14_cert).mp (by decide +kernel))

def profile8_node15_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 14 22 25 17), lower := (rows 23 14 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 12 20 8 16) }] }

theorem profile8_node15 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,18] 3 profile8_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12,18] 3 profile8_node15_cert).mp (by decide +kernel))

def profile8_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node13 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12] 3 (by decide) (choices 2) [17,18] profile8_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,12] (choices 2) [17,18] profile8_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node14
  · exact profile8_node15

def profile8_node17_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 23 19 7 28 28), lower := (rows 23 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile8_node17 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,3] 3 profile8_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,3] 3 profile8_node17_cert).mp (by decide +kernel))

def profile8_node18_cert : CutBound 5 := { lost := (rows 0 4 0 1 0), upper := (rows 23 19 13 30 22), lower := (rows 23 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 11 8 16) }] }

theorem profile8_node18 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,9] 3 profile8_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,9] 3 profile8_node18_cert).mp (by decide +kernel))

def profile8_node19_cert : CutBound 5 := { lost := (rows 0 4 0 2 0), upper := (rows 23 19 14 29 21), lower := (rows 23 19 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 10 8 16) }] }

theorem profile8_node19 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,10] 3 profile8_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,10] 3 profile8_node19_cert).mp (by decide +kernel))

def profile8_node20_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 23 19 21 14 30), lower := (rows 23 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 21 21 21 8 16) }] }

theorem profile8_node20 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,17] 3 profile8_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,17] 3 profile8_node20_cert).mp (by decide +kernel))

def profile8_node21_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 19 22 13 29), lower := (rows 23 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile8_node21 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,18] 3 profile8_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,18] 3 profile8_node21_cert).mp (by decide +kernel))

def profile8_node22_cert : CutBound 5 := { lost := (rows 0 4 0 16 0), upper := (rows 23 19 28 15 23), lower := (rows 23 19 28 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 24 8 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile8_node22 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,24] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,24] 3 profile8_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17,24] 3 profile8_node22_cert).mp (by decide +kernel))

def profile8_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node16 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile8_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,17] (choices 2) [3,9,10,17,18,24] profile8_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node17
  · exact profile8_node18
  · exact profile8_node19
  · exact profile8_node20
  · exact profile8_node21
  · exact profile8_node22

def profile8_node23_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 23 22 31 27 27), lower := (rows 23 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 22 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile8_node23 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,20] 3 profile8_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,20] 3 profile8_node23_cert).mp (by decide +kernel))

def profile8_node25_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 23 26 7 29 21), lower := (rows 23 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 7 10 7 8 0) }] }

theorem profile8_node25 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,3] 3 profile8_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,3] 3 profile8_node25_cert).mp (by decide +kernel))

def profile8_node26_cert : CutBound 5 := { lost := (rows 0 0 2 16 0), upper := (rows 23 26 21 15 23), lower := (rows 23 26 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 24 21 8 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 10 13 8 0) }] }

theorem profile8_node26 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,17] 3 profile8_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,17] 3 profile8_node26_cert).mp (by decide +kernel))

def profile8_node27_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 26 22 13 21), lower := (rows 23 26 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 20 8 16) }] }

theorem profile8_node27 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,18] 3 profile8_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24,18] 3 profile8_node27_cert).mp (by decide +kernel))

def profile8_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node24 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24] 3 (by decide) (choices 2) [3,17,18] profile8_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22,24] (choices 2) [3,17,18] profile8_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node25
  · exact profile8_node26
  · exact profile8_node27

def profile8_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node8 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile8_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [22] (choices 2) [5,9,12,17,20,24] profile8_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node9
  · exact profile8_node10
  · exact profile8_node13
  · exact profile8_node16
  · exact profile8_node23
  · exact profile8_node24

def profile8_node30_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 27 7 21 30 22), lower := (rows 27 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 21 8 16) }] }

theorem profile8_node30 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,17] 3 profile8_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,17] 3 profile8_node30_cert).mp (by decide +kernel))

def profile8_node31_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 27 7 22 29 21), lower := (rows 27 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) }] }

theorem profile8_node31 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,18] 3 profile8_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5,18] 3 profile8_node31_cert).mp (by decide +kernel))

def profile8_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node29 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5] 3 (by decide) (choices 2) [17,18] profile8_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,5] (choices 2) [17,18] profile8_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node30
  · exact profile8_node31

def profile8_node33_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 27 19 7 28 20), lower := (rows 27 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 18 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 17 29 8 16) }] }

theorem profile8_node33 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,3] 3 profile8_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,3] 3 profile8_node33_cert).mp (by decide +kernel))

def profile8_node34_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 27 19 21 14 22), lower := (rows 27 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 19 19 8 16) }] }

theorem profile8_node34 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,17] 3 profile8_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,17] 3 profile8_node34_cert).mp (by decide +kernel))

def profile8_node35_cert : CutBound 5 := { lost := (rows 0 4 1 0 0), upper := (rows 27 19 22 13 21), lower := (rows 27 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 18 8 16) }] }

theorem profile8_node35 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,18] 3 profile8_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17,18] 3 profile8_node35_cert).mp (by decide +kernel))

def profile8_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node32 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17] 3 (by decide) (choices 2) [3,17,18] profile8_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,17] (choices 2) [3,17,18] profile8_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node33
  · exact profile8_node34
  · exact profile8_node35

def profile8_node37_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 27 22 7 29 21), lower := (rows 27 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 7 8 0) }] }

theorem profile8_node37 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,3] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,3] 3 profile8_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,3] 3 profile8_node37_cert).mp (by decide +kernel))

def profile8_node38_cert : CutBound 5 := { lost := (rows 0 1 2 0 0), upper := (rows 27 22 21 15 23), lower := (rows 27 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 22 22 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 20 21 8 16) }] }

theorem profile8_node38 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,17] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,17] 3 profile8_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,17] 3 profile8_node38_cert).mp (by decide +kernel))

def profile8_node39_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 27 22 22 13 21), lower := (rows 27 22 22 8 16), losses := [{ target := 0, region := (rows 0 23 23 8 16), good := (rows 30 22 22 8 22) }] }

theorem profile8_node39 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,18] 3 :=
  cut_bound_sound (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,18] 3 profile8_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20,18] 3 profile8_node39_cert).mp (by decide +kernel))

def profile8_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node36 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20] 3 (by decide) (choices 2) [3,17,18] profile8_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26,20] (choices 2) [3,17,18] profile8_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node37
  · exact profile8_node38
  · exact profile8_node39

def profile8_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node28 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26] 3 (by decide) (choices 2) [5,17,20] profile8_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [26] (choices 2) [5,17,20] profile8_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node29
  · exact profile8_node32
  · exact profile8_node36

def profile8_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile8_node0 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [] 3 (by decide) (choices 3) [14,22,26] profile8_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [] (choices 3) [14,22,26] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile8_node1
  · exact profile8_node8
  · exact profile8_node28

theorem profile8 : Upper (D (n:=5) [50,34,34,33,19]) (R (n:=5) [50,34,34,33,19]) [] 3 := profile8_node0

def profile9_node3_cert : CutBound 5 := { lost := (rows 0 0 8 2 0), upper := (rows 15 19 22 28 28), lower := (rows 15 19 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) }] }

theorem profile9_node3 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,18] 3 profile9_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,18] 3 profile9_node3_cert).mp (by decide +kernel))

def profile9_node5_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 15 19 28 26 20), lower := (rows 15 19 28 26 16), losses := [{ target := 1, region := (rows 1 0 13 8 31), good := (rows 29 21 28 28 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 24 26 16) }] }

theorem profile9_node5 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,18] 3 profile9_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,18] 3 profile9_node5_cert).mp (by decide +kernel))

def profile9_node6_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 15 19 28 28 18), lower := (rows 15 19 28 28 16), losses := [{ target := 1, region := (rows 1 0 30 30 16), good := (rows 13 29 28 28 28) }] }

theorem profile9_node6 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,20] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,20] 3 profile9_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24,20] 3 profile9_node6_cert).mp (by decide +kernel))

def profile9_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node4 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24] 3 (by decide) (choices 2) [18,20] profile9_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17,24] (choices 2) [18,20] profile9_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node5
  · exact profile9_node6

def profile9_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node2 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17] 3 (by decide) (choices 2) [18,24] profile9_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,17] (choices 2) [18,24] profile9_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node3
  · exact profile9_node4

def profile9_node8_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 22 21 26 26), lower := (rows 15 22 21 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) }] }

theorem profile9_node8 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,17] 3 profile9_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,17] 3 profile9_node8_cert).mp (by decide +kernel))

def profile9_node9_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 15 22 22 25 25), lower := (rows 15 22 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 20 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 18 8 16) }] }

theorem profile9_node9 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,18] 3 profile9_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,18] 3 profile9_node9_cert).mp (by decide +kernel))

def profile9_node10_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 22 28 27 19), lower := (rows 15 22 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 24 8 16) },{ target := 3, region := (rows 1 7 4 0 17), good := (rows 23 22 22 0 16) }] }

theorem profile9_node10 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,24] 3 profile9_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20,24] 3 profile9_node10_cert).mp (by decide +kernel))

def profile9_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node7 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20] 3 (by decide) (choices 2) [17,18,24] profile9_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14,20] (choices 2) [17,18,24] profile9_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node8
  · exact profile9_node9
  · exact profile9_node10

def profile9_node1_route : Route 5 := (fun mask => match mask with | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile9_node1 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14] 3 (by decide) (choices 2) [17,20] profile9_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [14] (choices 2) [17,20] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node2
  · exact profile9_node7

def profile9_node12_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 23 7 30 26 26), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile9_node12 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,5] 3 profile9_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,5] 3 profile9_node12_cert).mp (by decide +kernel))

def profile9_node14_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 11 22 28 28), lower := (rows 23 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile9_node14 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,18] 3 profile9_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,18] 3 profile9_node14_cert).mp (by decide +kernel))

def profile9_node16_cert : CutBound 5 := { lost := (rows 0 4 2 4 0), upper := (rows 23 11 28 26 20), lower := (rows 23 11 28 26 16), losses := [{ target := 1, region := (rows 1 0 14 8 31), good := (rows 21 29 28 28 16) },{ target := 2, region := (rows 1 3 0 9 16), good := (rows 27 11 24 26 16) }] }

theorem profile9_node16 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,18] 3 profile9_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,18] 3 profile9_node16_cert).mp (by decide +kernel))

def profile9_node17_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 23 11 28 28 18), lower := (rows 23 11 28 28 16), losses := [{ target := 1, region := (rows 1 0 29 29 16), good := (rows 29 13 28 28 28) }] }

theorem profile9_node17 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,20] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,20] 3 profile9_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24,20] 3 profile9_node17_cert).mp (by decide +kernel))

def profile9_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node15 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24] 3 (by decide) (choices 2) [18,20] profile9_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9,24] (choices 2) [18,20] profile9_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node16
  · exact profile9_node17

def profile9_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node13 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9] 3 (by decide) (choices 2) [18,24] profile9_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,9] (choices 2) [18,24] profile9_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node14
  · exact profile9_node15

def profile9_node19_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 23 14 21 26 26), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 26 25 8 16) }] }

theorem profile9_node19 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,17] 3 profile9_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,17] 3 profile9_node19_cert).mp (by decide +kernel))

def profile9_node20_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 23 14 22 25 25), lower := (rows 23 14 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 12 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 18 8 16) }] }

theorem profile9_node20 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,18] 3 profile9_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,18] 3 profile9_node20_cert).mp (by decide +kernel))

def profile9_node21_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 14 28 27 19), lower := (rows 23 14 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 24 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile9_node21 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,24] 3 profile9_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12,24] 3 profile9_node21_cert).mp (by decide +kernel))

def profile9_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node18 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12] 3 (by decide) (choices 2) [17,18,24] profile9_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,12] (choices 2) [17,18,24] profile9_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node19
  · exact profile9_node20
  · exact profile9_node21

def profile9_node22_cert : CutBound 5 := { lost := (rows 0 12 0 0 0), upper := (rows 23 19 30 30 30), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) }] }

theorem profile9_node22 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,17] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,17] 3 profile9_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,17] 3 profile9_node22_cert).mp (by decide +kernel))

def profile9_node23_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 22 31 27 27), lower := (rows 23 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile9_node23 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,20] 3 profile9_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,20] 3 profile9_node23_cert).mp (by decide +kernel))

def profile9_node25_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 26 7 28 28), lower := (rows 23 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile9_node25 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,3] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,3] 3 profile9_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,3] 3 profile9_node25_cert).mp (by decide +kernel))

def profile9_node27_cert : CutBound 5 := { lost := (rows 0 4 0 4 0), upper := (rows 23 26 13 26 20), lower := (rows 23 26 13 26 16), losses := [{ target := 2, region := (rows 1 27 0 27 16), good := (rows 27 26 11 26 26) }] }

theorem profile9_node27 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,18] 3 profile9_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,18] 3 profile9_node27_cert).mp (by decide +kernel))

def profile9_node28_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 23 26 13 28 18), lower := (rows 23 26 13 28 16), losses := [{ target := 1, region := (rows 1 0 5 9 16), good := (rows 29 24 13 28 16) }] }

theorem profile9_node28 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,20] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,20] 3 profile9_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9,20] 3 profile9_node28_cert).mp (by decide +kernel))

def profile9_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node26 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9] 3 (by decide) (choices 2) [18,20] profile9_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,9] (choices 2) [18,20] profile9_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node27
  · exact profile9_node28

def profile9_node29_cert : CutBound 5 := { lost := (rows 8 0 0 2 0), upper := (rows 23 26 14 29 21), lower := (rows 23 26 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 18 23 0 16) }] }

theorem profile9_node29 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,10] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,10] 3 profile9_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,10] 3 profile9_node29_cert).mp (by decide +kernel))

def profile9_node30_cert : CutBound 5 := { lost := (rows 8 0 10 0 0), upper := (rows 23 26 21 14 30), lower := (rows 23 26 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 24 21 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 21 0 16) }] }

theorem profile9_node30 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,17] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,17] 3 profile9_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,17] 3 profile9_node30_cert).mp (by decide +kernel))

def profile9_node31_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 26 22 13 29), lower := (rows 23 26 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 20 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile9_node31 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,18] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,18] 3 profile9_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,18] 3 profile9_node31_cert).mp (by decide +kernel))

def profile9_node32_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 23 26 28 15 23), lower := (rows 23 26 28 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 28 28 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 26 26 8 16) }] }

theorem profile9_node32 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,24] 3 :=
  cut_bound_sound (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,24] 3 profile9_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24,24] 3 profile9_node32_cert).mp (by decide +kernel))

def profile9_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node24 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile9_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22,24] (choices 2) [3,9,10,17,18,24] profile9_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node25
  · exact profile9_node26
  · exact profile9_node29
  · exact profile9_node30
  · exact profile9_node31
  · exact profile9_node32

def profile9_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node11 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile9_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [22] (choices 2) [5,9,12,17,20,24] profile9_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node12
  · exact profile9_node13
  · exact profile9_node18
  · exact profile9_node22
  · exact profile9_node23
  · exact profile9_node24

def profile9_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile9_node0 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [] 3 (by decide) (choices 3) [14,22] profile9_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [] (choices 3) [14,22] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node1
  · exact profile9_node11

theorem profile9 : Upper (D (n:=5) [49,34,34,34,19]) (R (n:=5) [49,34,34,34,19]) [] 3 := profile9_node0

#print axioms profile9
end Delivery.FiveVertexPositive10
