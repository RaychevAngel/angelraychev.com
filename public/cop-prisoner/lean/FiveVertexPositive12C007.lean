import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile93_node4_cert : CutBound 5 := { lost := (rows 16 16 2 1 3), upper := (rows 15 15 21 26 28), lower := (rows 15 15 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 23), good := (rows 30 30 28 26 16) },{ target := 1, region := (rows 1 0 7 8 27), good := (rows 29 29 21 28 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 11 0) }] }

theorem profile93_node4 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,18] 2 profile93_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,18] 2 profile93_node4_cert).mp (by decide +kernel))

def profile93_node5_cert : CutBound 5 := { lost := (rows 16 16 0 3 5), upper := (rows 15 15 21 28 26), lower := (rows 15 15 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 15 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 24 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile93_node5 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,20] 2 profile93_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17,20] 2 profile93_node5_cert).mp (by decide +kernel))

def profile93_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node3 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17] 2 (by decide) (choices 2) [18,20] profile93_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,17] (choices 2) [18,20] profile93_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node4
  · exact profile93_node5

def profile93_node7_cert : CutBound 5 := { lost := (rows 16 16 1 2 3), upper := (rows 15 15 22 25 28), lower := (rows 15 15 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 27), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 11 23), good := (rows 29 29 28 25 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 11 0) }] }

theorem profile93_node7 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,17] 2 profile93_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,17] 2 profile93_node7_cert).mp (by decide +kernel))

def profile93_node8_cert : CutBound 5 := { lost := (rows 16 16 0 3 6), upper := (rows 15 15 22 28 25), lower := (rows 15 15 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 30 28 16) },{ target := 1, region := (rows 1 0 4 15 19), good := (rows 29 29 28 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 18 24 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile93_node8 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,20] 2 profile93_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18,20] 2 profile93_node8_cert).mp (by decide +kernel))

def profile93_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node6 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18] 2 (by decide) (choices 2) [17,20] profile93_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,18] (choices 2) [17,20] profile93_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node7
  · exact profile93_node8

def profile93_node10_cert : CutBound 5 := { lost := (rows 16 16 3 0 9), upper := (rows 15 15 28 25 22), lower := (rows 15 15 28 25 16), losses := [{ target := 0, region := (rows 0 2 15 8 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 13 13 28 29 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 17 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 11 0) }] }

theorem profile93_node10 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,17] 2 profile93_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,17] 2 profile93_node10_cert).mp (by decide +kernel))

def profile93_node11_cert : CutBound 5 := { lost := (rows 16 16 3 0 10), upper := (rows 15 15 28 26 21), lower := (rows 15 15 28 26 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 14 14 28 30 16) },{ target := 1, region := (rows 1 0 15 8 19), good := (rows 29 29 28 28 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 18 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 11 0) }] }

theorem profile93_node11 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,18] 2 profile93_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,18] 2 profile93_node11_cert).mp (by decide +kernel))

def profile93_node12_cert : CutBound 5 := { lost := (rows 0 0 3 3 12), upper := (rows 15 15 28 28 19), lower := (rows 15 15 28 28 16), losses := [{ target := 0, region := (rows 0 2 28 28 16), good := (rows 14 14 28 28 28) },{ target := 1, region := (rows 1 0 28 28 16), good := (rows 13 13 28 28 28) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 24 24 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 20 16) }] }

theorem profile93_node12 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,20] 2 profile93_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24,20] 2 profile93_node12_cert).mp (by decide +kernel))

def profile93_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node9 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24] 2 (by decide) (choices 2) [17,18,20] profile93_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13,24] (choices 2) [17,18,20] profile93_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node10
  · exact profile93_node11
  · exact profile93_node12

def profile93_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node2 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13] 2 (by decide) (choices 2) [17,18,24] profile93_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,13] (choices 2) [17,18,24] profile93_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node3
  · exact profile93_node6
  · exact profile93_node9

def profile93_node15_cert : CutBound 5 := { lost := (rows 16 0 18 5 3), upper := (rows 15 23 13 26 28), lower := (rows 15 23 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 23), good := (rows 30 30 28 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 26 16) },{ target := 4, region := (rows 9 2 13 8 0), good := (rows 15 7 13 15 0) }] }

theorem profile93_node15 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,18] 2 profile93_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,18] 2 profile93_node15_cert).mp (by decide +kernel))

def profile93_node16_cert : CutBound 5 := { lost := (rows 0 0 18 3 5), upper := (rows 15 23 13 28 26), lower := (rows 15 23 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 15 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 7 10 16), good := (rows 13 29 13 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 25 24 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 12 0) }] }

theorem profile93_node16 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,20] 2 profile93_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9,20] 2 profile93_node16_cert).mp (by decide +kernel))

def profile93_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node14 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9] 2 (by decide) (choices 2) [18,20] profile93_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,9] (choices 2) [18,20] profile93_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node15
  · exact profile93_node16

def profile93_node18_cert : CutBound 5 := { lost := (rows 16 0 17 6 3), upper := (rows 15 23 14 25 28), lower := (rows 15 23 14 25 16), losses := [{ target := 0, region := (rows 0 2 5 8 29), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 11 23), good := (rows 29 29 28 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 10 25 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 13 0) }] }

theorem profile93_node18 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,17] 2 profile93_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,17] 2 profile93_node18_cert).mp (by decide +kernel))

def profile93_node19_cert : CutBound 5 := { lost := (rows 16 0 17 3 6), upper := (rows 15 23 14 28 25), lower := (rows 15 23 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 10 16), good := (rows 14 30 14 28 16) },{ target := 1, region := (rows 1 0 4 15 19), good := (rows 29 29 28 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 10 24 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 13 0) }] }

theorem profile93_node19 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,20] 2 profile93_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10,20] 2 profile93_node19_cert).mp (by decide +kernel))

def profile93_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node17 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10] 2 (by decide) (choices 2) [17,20] profile93_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,10] (choices 2) [17,20] profile93_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node18
  · exact profile93_node19

def profile93_node21_cert : CutBound 5 := { lost := (rows 16 0 3 20 3), upper := (rows 15 23 28 11 28), lower := (rows 15 23 28 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 29), good := (rows 30 22 28 30 16) },{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 21 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 11 0) }] }

theorem profile93_node21 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,3] 2 profile93_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,3] 2 profile93_node21_cert).mp (by decide +kernel))

def profile93_node22_cert : CutBound 5 := { lost := (rows 16 0 3 18 5), upper := (rows 15 23 28 13 26), lower := (rows 15 23 28 13 16), losses := [{ target := 0, region := (rows 0 2 13 8 17), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 24 25 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 13 0) }] }

theorem profile93_node22 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,5] 2 profile93_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,5] 2 profile93_node22_cert).mp (by decide +kernel))

def profile93_node23_cert : CutBound 5 := { lost := (rows 16 0 3 17 6), upper := (rows 15 23 28 14 25), lower := (rows 15 23 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) },{ target := 1, region := (rows 1 0 5 8 17), good := (rows 29 21 28 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 24 10 16) },{ target := 4, region := (rows 11 2 4 11 0), good := (rows 15 15 13 15 0) }] }

theorem profile93_node23 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,6] 2 profile93_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24,6] 2 profile93_node23_cert).mp (by decide +kernel))

def profile93_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node20 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24] 2 (by decide) (choices 2) [3,5,6] profile93_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21,24] (choices 2) [3,5,6] profile93_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node21
  · exact profile93_node22
  · exact profile93_node23

def profile93_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node13 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21] 2 (by decide) (choices 2) [9,10,24] profile93_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,21] (choices 2) [9,10,24] profile93_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node14
  · exact profile93_node17
  · exact profile93_node20

def profile93_node26_cert : CutBound 5 := { lost := (rows 16 1 24 2 3), upper := (rows 15 30 7 25 28), lower := (rows 15 30 7 25 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 13 23), good := (rows 29 28 29 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 21 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 13 0) }] }

theorem profile93_node26 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,17] 2 profile93_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,17] 2 profile93_node26_cert).mp (by decide +kernel))

def profile93_node27_cert : CutBound 5 := { lost := (rows 0 1 8 3 6), upper := (rows 15 30 7 28 25), lower := (rows 15 30 7 28 16), losses := [{ target := 0, region := (rows 0 10 4 10 16), good := (rows 14 30 14 30 16) },{ target := 1, region := (rows 1 0 4 15 21), good := (rows 29 28 29 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 19 24 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 20 16) }] }

theorem profile93_node27 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,20] 2 profile93_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3,20] 2 profile93_node27_cert).mp (by decide +kernel))

def profile93_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node25 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3] 2 (by decide) (choices 2) [17,20] profile93_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,3] (choices 2) [17,20] profile93_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node26
  · exact profile93_node27

def profile93_node29_cert : CutBound 5 := { lost := (rows 16 1 18 0 9), upper := (rows 15 30 13 25 22), lower := (rows 15 30 13 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 1 0 13 8 16), good := (rows 13 28 13 29 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 22 21 17 16) },{ target := 4, region := (rows 3 2 15 8 0), good := (rows 15 15 13 13 0) }] }

theorem profile93_node29 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,17] 2 profile93_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,17] 2 profile93_node29_cert).mp (by decide +kernel))

def profile93_node30_cert : CutBound 5 := { lost := (rows 16 0 18 5 10), upper := (rows 15 30 13 26 21), lower := (rows 15 30 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 12 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 26 9 26 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 21 18 16) },{ target := 4, region := (rows 11 2 15 8 0), good := (rows 15 15 13 15 0) }] }

theorem profile93_node30 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,18] 2 profile93_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,18] 2 profile93_node30_cert).mp (by decide +kernel))

def profile93_node31_cert : CutBound 5 := { lost := (rows 0 1 2 3 12), upper := (rows 15 30 13 28 19), lower := (rows 15 30 13 28 16), losses := [{ target := 0, region := (rows 0 10 4 10 16), good := (rows 14 30 14 30 16) },{ target := 1, region := (rows 1 0 5 10 16), good := (rows 13 28 13 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 25 24 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 20 16) }] }

theorem profile93_node31 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,20] 2 profile93_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9,20] 2 profile93_node31_cert).mp (by decide +kernel))

def profile93_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node28 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9] 2 (by decide) (choices 2) [17,18,20] profile93_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,9] (choices 2) [17,18,20] profile93_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node29
  · exact profile93_node30
  · exact profile93_node31

def profile93_node32_cert : CutBound 5 := { lost := (rows 16 0 17 2 10), upper := (rows 15 30 14 29 21), lower := (rows 15 30 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 14 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 6 0 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile93_node32 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,10] 2 profile93_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,10] 2 profile93_node32_cert).mp (by decide +kernel))

def profile93_node34_cert : CutBound 5 := { lost := (rows 16 1 2 20 3), upper := (rows 15 30 21 11 28), lower := (rows 15 30 21 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 13 8 27), good := (rows 29 28 21 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 11 26 25 11 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 11 0) }] }

theorem profile93_node34 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,3] 2 profile93_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,3] 2 profile93_node34_cert).mp (by decide +kernel))

def profile93_node35_cert : CutBound 5 := { lost := (rows 16 1 0 18 5), upper := (rows 15 30 21 13 26), lower := (rows 15 30 21 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 29 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 26 17 25 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile93_node35 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,5] 2 profile93_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,5] 2 profile93_node35_cert).mp (by decide +kernel))

def profile93_node36_cert : CutBound 5 := { lost := (rows 16 1 2 17 6), upper := (rows 15 30 21 14 25), lower := (rows 15 30 21 14 16), losses := [{ target := 0, region := (rows 0 6 4 15 16), good := (rows 14 30 30 14 16) },{ target := 1, region := (rows 1 0 5 8 17), good := (rows 29 28 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 17 10 16) },{ target := 4, region := (rows 11 2 4 11 0), good := (rows 15 15 13 15 0) }] }

theorem profile93_node36 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,6] 2 profile93_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17,6] 2 profile93_node36_cert).mp (by decide +kernel))

def profile93_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node33 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17] 2 (by decide) (choices 2) [3,5,6] profile93_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,17] (choices 2) [3,5,6] profile93_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node34
  · exact profile93_node35
  · exact profile93_node36

def profile93_node37_cert : CutBound 5 := { lost := (rows 16 0 9 18 2), upper := (rows 15 30 22 13 29), lower := (rows 15 30 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 22 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile93_node37 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,18] 2 profile93_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,18] 2 profile93_node37_cert).mp (by decide +kernel))

def profile93_node38_cert : CutBound 5 := { lost := (rows 16 1 3 16 8), upper := (rows 15 30 28 15 23), lower := (rows 15 30 28 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 28 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile93_node38 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,24] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,24] 2 profile93_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28,24] 2 profile93_node38_cert).mp (by decide +kernel))

def profile93_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node24 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile93_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14,28] (choices 2) [3,9,10,17,18,24] profile93_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile93_node25
  · exact profile93_node28
  · exact profile93_node32
  · exact profile93_node33
  · exact profile93_node37
  · exact profile93_node38

def profile93_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile93_node1 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile93_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [14] (choices 3) [13,21,28] profile93_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node2
  · exact profile93_node13
  · exact profile93_node24

def profile93_node42_cert : CutBound 5 := { lost := (rows 0 16 18 5 3), upper := (rows 23 15 13 26 28), lower := (rows 23 15 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 23), good := (rows 30 30 28 26 16) },{ target := 1, region := (rows 1 0 6 8 30), good := (rows 21 29 29 28 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 9 26 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 14 0) }] }

theorem profile93_node42 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,18] 2 profile93_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,18] 2 profile93_node42_cert).mp (by decide +kernel))

def profile93_node43_cert : CutBound 5 := { lost := (rows 0 16 18 3 5), upper := (rows 23 15 13 28 26), lower := (rows 23 15 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 15 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 7 9 16), good := (rows 29 13 13 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 9 24 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 14 0) }] }

theorem profile93_node43 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,20] 2 profile93_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9,20] 2 profile93_node43_cert).mp (by decide +kernel))

def profile93_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node41 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9] 2 (by decide) (choices 2) [18,20] profile93_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,9] (choices 2) [18,20] profile93_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node42
  · exact profile93_node43

def profile93_node45_cert : CutBound 5 := { lost := (rows 0 16 17 6 3), upper := (rows 23 15 14 25 28), lower := (rows 23 15 14 25 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 22 30 30 24 16) },{ target := 1, region := (rows 1 0 4 11 23), good := (rows 29 29 28 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 25 16) },{ target := 4, region := (rows 1 10 14 8 0), good := (rows 7 15 14 15 0) }] }

theorem profile93_node45 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,17] 2 profile93_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,17] 2 profile93_node45_cert).mp (by decide +kernel))

def profile93_node46_cert : CutBound 5 := { lost := (rows 0 0 17 3 6), upper := (rows 23 15 14 28 25), lower := (rows 23 15 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 15 19), good := (rows 29 29 28 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 26 24 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 14 12 0) }] }

theorem profile93_node46 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,20] 2 profile93_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10,20] 2 profile93_node46_cert).mp (by decide +kernel))

def profile93_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node44 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10] 2 (by decide) (choices 2) [17,20] profile93_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,10] (choices 2) [17,20] profile93_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node45
  · exact profile93_node46

def profile93_node48_cert : CutBound 5 := { lost := (rows 0 16 3 20 3), upper := (rows 23 15 28 11 28), lower := (rows 23 15 28 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 30), good := (rows 22 30 28 30 16) },{ target := 1, region := (rows 1 0 14 8 30), good := (rows 21 29 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 24 11 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 11 0) }] }

theorem profile93_node48 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,3] 2 profile93_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,3] 2 profile93_node48_cert).mp (by decide +kernel))

def profile93_node49_cert : CutBound 5 := { lost := (rows 0 16 3 18 5), upper := (rows 23 15 28 13 26), lower := (rows 23 15 28 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 18), good := (rows 22 30 28 12 16) },{ target := 1, region := (rows 1 0 5 11 16), good := (rows 29 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 24 9 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile93_node49 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,5] 2 profile93_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,5] 2 profile93_node49_cert).mp (by decide +kernel))

def profile93_node50_cert : CutBound 5 := { lost := (rows 0 16 3 17 6), upper := (rows 23 15 28 14 25), lower := (rows 23 15 28 14 16), losses := [{ target := 0, region := (rows 0 2 5 11 16), good := (rows 30 14 28 14 16) },{ target := 1, region := (rows 1 0 14 8 18), good := (rows 21 29 28 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 24 26 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 14 0) }] }

theorem profile93_node50 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,6] 2 profile93_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24,6] 2 profile93_node50_cert).mp (by decide +kernel))

def profile93_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node47 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24] 2 (by decide) (choices 2) [3,5,6] profile93_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13,24] (choices 2) [3,5,6] profile93_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node48
  · exact profile93_node49
  · exact profile93_node50

def profile93_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node40 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13] 2 (by decide) (choices 2) [9,10,24] profile93_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,13] (choices 2) [9,10,24] profile93_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node41
  · exact profile93_node44
  · exact profile93_node47

def profile93_node53_cert : CutBound 5 := { lost := (rows 0 0 18 17 3), upper := (rows 23 27 13 14 28), lower := (rows 23 27 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 29), good := (rows 30 26 28 30 16) },{ target := 1, region := (rows 1 0 6 8 30), good := (rows 21 29 29 28 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 14 0) }] }

theorem profile93_node53 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9,6] 2 profile93_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9,6] 2 profile93_node53_cert).mp (by decide +kernel))

def profile93_node52_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node52 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9] 2 (by decide) (choices 2) [6] profile93_node52_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,9] (choices 2) [6] profile93_node52_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node53

def profile93_node55_cert : CutBound 5 := { lost := (rows 0 0 17 18 3), upper := (rows 23 27 14 13 28), lower := (rows 23 27 14 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 30), good := (rows 22 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 29), good := (rows 29 25 28 29 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 13 0) }] }

theorem profile93_node55 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10,5] 2 profile93_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10,5] 2 profile93_node55_cert).mp (by decide +kernel))

def profile93_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node54 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10] 2 (by decide) (choices 2) [5] profile93_node54_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25,10] (choices 2) [5] profile93_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node55

def profile93_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node51 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25] 2 (by decide) (choices 2) [9,10] profile93_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,25] (choices 2) [9,10] profile93_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node52
  · exact profile93_node54

def profile93_node58_cert : CutBound 5 := { lost := (rows 8 1 2 4 3), upper := (rows 23 30 13 11 28), lower := (rows 23 30 13 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 22 30 30 26 16) },{ target := 1, region := (rows 1 0 12 8 30), good := (rows 21 28 29 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 26 9 11 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 5 3 16) }] }

theorem profile93_node58 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,3] 2 profile93_node58_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,3] 2 profile93_node58_cert).mp (by decide +kernel))

def profile93_node59_cert : CutBound 5 := { lost := (rows 8 1 2 2 5), upper := (rows 23 30 13 13 26), lower := (rows 23 30 13 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 30), good := (rows 22 30 30 30 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 29 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 26 9 9 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 5 5 16) }] }

theorem profile93_node59 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,5] 2 profile93_node59_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,5] 2 profile93_node59_cert).mp (by decide +kernel))

def profile93_node60_cert : CutBound 5 := { lost := (rows 8 1 16 17 6), upper := (rows 23 30 13 14 25), lower := (rows 23 30 13 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 28 29 28 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 19 26 25 26 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 5 7 16) },{ target := 4, region := (rows 1 2 5 11 0), good := (rows 15 14 13 14 0) }] }

theorem profile93_node60 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,6] 2 profile93_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9,6] 2 profile93_node60_cert).mp (by decide +kernel))

def profile93_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node57 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9] 2 (by decide) (choices 2) [3,5,6] profile93_node57_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,9] (choices 2) [3,5,6] profile93_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node58
  · exact profile93_node59
  · exact profile93_node60

def profile93_node61_cert : CutBound 5 := { lost := (rows 8 0 17 18 2), upper := (rows 23 30 14 13 29), lower := (rows 23 30 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile93_node61 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,10] 2 profile93_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28,10] 2 profile93_node61_cert).mp (by decide +kernel))

def profile93_node56_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node56 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28] 2 (by decide) (choices 2) [9,10] profile93_node56_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22,28] (choices 2) [9,10] profile93_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node57
  · exact profile93_node61

def profile93_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node39 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22] 2 (by decide) (choices 3) [13,25,28] profile93_node39_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [22] (choices 3) [13,25,28] profile93_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node40
  · exact profile93_node51
  · exact profile93_node56

def profile93_node65_cert : CutBound 5 := { lost := (rows 2 16 24 1 3), upper := (rows 29 15 7 26 28), lower := (rows 29 15 7 26 16), losses := [{ target := 0, region := (rows 0 2 4 14 23), good := (rows 28 30 30 26 16) },{ target := 1, region := (rows 3 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 7 7 22 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 14 0) }] }

theorem profile93_node65 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,18] 2 profile93_node65_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,18] 2 profile93_node65_cert).mp (by decide +kernel))

def profile93_node66_cert : CutBound 5 := { lost := (rows 2 0 8 3 5), upper := (rows 29 15 7 28 26), lower := (rows 29 15 7 28 16), losses := [{ target := 0, region := (rows 0 2 4 15 22), good := (rows 28 30 30 28 16) },{ target := 1, region := (rows 9 0 4 9 16), good := (rows 29 13 13 29 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 19 24 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 7 7 20 16) }] }

theorem profile93_node66 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,20] 2 profile93_node66_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3,20] 2 profile93_node66_cert).mp (by decide +kernel))

def profile93_node64_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node64 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3] 2 (by decide) (choices 2) [18,20] profile93_node64_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,3] (choices 2) [18,20] profile93_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node65
  · exact profile93_node66

def profile93_node67_cert : CutBound 5 := { lost := (rows 0 16 18 1 9), upper := (rows 29 15 13 30 22), lower := (rows 29 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 12 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 5 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile93_node67 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,9] 2 profile93_node67_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,9] 2 profile93_node67_cert).mp (by decide +kernel))

def profile93_node69_cert : CutBound 5 := { lost := (rows 0 16 17 6 9), upper := (rows 29 15 14 25 22), lower := (rows 29 15 14 25 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 28 30 30 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 12 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 25 11 10 25 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 23 22 17 16) },{ target := 4, region := (rows 1 11 15 8 0), good := (rows 15 15 14 15 0) }] }

theorem profile93_node69 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,17] 2 profile93_node69_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,17] 2 profile93_node69_cert).mp (by decide +kernel))

def profile93_node70_cert : CutBound 5 := { lost := (rows 2 16 17 0 10), upper := (rows 29 15 14 26 21), lower := (rows 29 15 14 26 16), losses := [{ target := 0, region := (rows 0 2 14 8 16), good := (rows 28 14 14 30 16) },{ target := 1, region := (rows 7 0 4 8 23), good := (rows 29 29 29 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 21 23 22 18 16) },{ target := 4, region := (rows 1 3 15 8 0), good := (rows 15 15 14 14 0) }] }

theorem profile93_node70 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,18] 2 profile93_node70_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,18] 2 profile93_node70_cert).mp (by decide +kernel))

def profile93_node71_cert : CutBound 5 := { lost := (rows 2 0 1 3 12), upper := (rows 29 15 14 28 19), lower := (rows 29 15 14 28 16), losses := [{ target := 0, region := (rows 0 2 6 9 16), good := (rows 28 14 14 28 16) },{ target := 1, region := (rows 9 0 4 9 16), good := (rows 29 13 13 29 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 26 24 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 22 20 16) }] }

theorem profile93_node71 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,20] 2 profile93_node71_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10,20] 2 profile93_node71_cert).mp (by decide +kernel))

def profile93_node68_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node68 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10] 2 (by decide) (choices 2) [17,18,20] profile93_node68_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,10] (choices 2) [17,18,20] profile93_node68_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node69
  · exact profile93_node70
  · exact profile93_node71

def profile93_node72_cert : CutBound 5 := { lost := (rows 0 16 10 17 1), upper := (rows 29 15 21 14 30), lower := (rows 29 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 21 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile93_node72 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,17] 2 profile93_node72_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,17] 2 profile93_node72_cert).mp (by decide +kernel))

def profile93_node74_cert : CutBound 5 := { lost := (rows 2 16 1 20 3), upper := (rows 29 15 22 11 28), lower := (rows 29 15 22 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 27), good := (rows 28 30 22 30 16) },{ target := 1, region := (rows 3 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 11 26 11 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 11 0) }] }

theorem profile93_node74 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,3] 2 profile93_node74_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,3] 2 profile93_node74_cert).mp (by decide +kernel))

def profile93_node75_cert : CutBound 5 := { lost := (rows 2 16 1 18 5), upper := (rows 29 15 22 13 26), lower := (rows 29 15 22 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 18), good := (rows 28 30 22 12 16) },{ target := 1, region := (rows 5 0 4 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 18 9 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile93_node75 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,5] 2 profile93_node75_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,5] 2 profile93_node75_cert).mp (by decide +kernel))

def profile93_node76_cert : CutBound 5 := { lost := (rows 2 16 0 17 6), upper := (rows 29 15 22 14 25), lower := (rows 29 15 22 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 28 14 30 14 16) },{ target := 1, region := (rows 11 0 4 8 27), good := (rows 29 29 21 29 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 25 27 18 26 16) },{ target := 4, region := (rows 1 3 4 15 0), good := (rows 15 15 14 14 0) }] }

theorem profile93_node76 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,6] 2 profile93_node76_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18,6] 2 profile93_node76_cert).mp (by decide +kernel))

def profile93_node73_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node73 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18] 2 (by decide) (choices 2) [3,5,6] profile93_node73_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,18] (choices 2) [3,5,6] profile93_node73_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node74
  · exact profile93_node75
  · exact profile93_node76

def profile93_node77_cert : CutBound 5 := { lost := (rows 2 16 3 16 8), upper := (rows 29 15 28 15 23), lower := (rows 29 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 28 14 28 8 16) },{ target := 1, region := (rows 5 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile93_node77 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,24] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,24] 2 profile93_node77_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13,24] 2 profile93_node77_cert).mp (by decide +kernel))

def profile93_node63_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node63 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile93_node63_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,13] (choices 2) [3,9,10,17,18,24] profile93_node63_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile93_node64
  · exact profile93_node67
  · exact profile93_node68
  · exact profile93_node72
  · exact profile93_node73
  · exact profile93_node77

def profile93_node79_cert : CutBound 5 := { lost := (rows 0 8 18 17 1), upper := (rows 29 23 13 14 30), lower := (rows 29 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 12 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 10 0), good := (rows 13 15 13 8 0) }] }

theorem profile93_node79 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,9] 2 profile93_node79_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,9] 2 profile93_node79_cert).mp (by decide +kernel))

def profile93_node81_cert : CutBound 5 := { lost := (rows 2 8 1 4 3), upper := (rows 29 23 14 11 28), lower := (rows 29 23 14 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 29), good := (rows 28 22 30 30 16) },{ target := 1, region := (rows 5 0 4 8 21), good := (rows 29 21 29 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 27 10 11 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 3 16) }] }

theorem profile93_node81 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,3] 2 profile93_node81_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,3] 2 profile93_node81_cert).mp (by decide +kernel))

def profile93_node82_cert : CutBound 5 := { lost := (rows 2 8 16 18 5), upper := (rows 29 23 14 13 26), lower := (rows 29 23 14 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 28 22 30 28 16) },{ target := 1, region := (rows 3 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 25 19 26 25 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 7 16) },{ target := 4, region := (rows 1 2 6 11 0), good := (rows 13 15 14 13 0) }] }

theorem profile93_node82 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,5] 2 profile93_node82_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,5] 2 profile93_node82_cert).mp (by decide +kernel))

def profile93_node83_cert : CutBound 5 := { lost := (rows 2 8 1 1 6), upper := (rows 29 23 14 14 25), lower := (rows 29 23 14 14 16), losses := [{ target := 0, region := (rows 0 2 14 14 16), good := (rows 28 30 14 14 16) },{ target := 1, region := (rows 13 0 4 8 29), good := (rows 29 21 29 29 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 25 19 10 10 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 6 16) }] }

theorem profile93_node83 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,6] 2 profile93_node83_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10,6] 2 profile93_node83_cert).mp (by decide +kernel))

def profile93_node80_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node80 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10] 2 (by decide) (choices 2) [3,5,6] profile93_node80_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21,10] (choices 2) [3,5,6] profile93_node80_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node81
  · exact profile93_node82
  · exact profile93_node83

def profile93_node78_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node78 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21] 2 (by decide) (choices 2) [9,10] profile93_node78_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,21] (choices 2) [9,10] profile93_node78_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node79
  · exact profile93_node80

def profile93_node86_cert : CutBound 5 := { lost := (rows 2 1 8 4 3), upper := (rows 29 30 7 11 28), lower := (rows 29 30 7 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 3 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 25 26 11 11 16) },{ target := 3, region := (rows 1 2 12 0 16), good := (rows 21 22 7 7 16) }] }

theorem profile93_node86 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,3] 2 profile93_node86_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,3] 2 profile93_node86_cert).mp (by decide +kernel))

def profile93_node87_cert : CutBound 5 := { lost := (rows 2 1 0 18 5), upper := (rows 29 30 7 13 26), lower := (rows 29 30 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 3 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 26 19 9 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 13 0) }] }

theorem profile93_node87 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,5] 2 profile93_node87_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,5] 2 profile93_node87_cert).mp (by decide +kernel))

def profile93_node88_cert : CutBound 5 := { lost := (rows 2 1 0 17 6), upper := (rows 29 30 7 14 25), lower := (rows 29 30 7 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 11 0 4 8 27), good := (rows 29 29 21 29 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 25 26 19 10 16) },{ target := 4, region := (rows 1 2 4 14 0), good := (rows 13 14 15 14 0) }] }

theorem profile93_node88 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,6] 2 profile93_node88_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3,6] 2 profile93_node88_cert).mp (by decide +kernel))

def profile93_node85_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node85 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3] 2 (by decide) (choices 2) [3,5,6] profile93_node85_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,3] (choices 2) [3,5,6] profile93_node85_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node86
  · exact profile93_node87
  · exact profile93_node88

def profile93_node90_cert : CutBound 5 := { lost := (rows 2 1 18 0 9), upper := (rows 29 30 13 11 22), lower := (rows 29 30 13 11 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 3 0 15 8 16), good := (rows 29 29 13 13 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 22 5 19 16) },{ target := 4, region := (rows 1 2 13 8 0), good := (rows 13 14 13 15 0) }] }

theorem profile93_node90 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,3] 2 profile93_node90_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,3] 2 profile93_node90_cert).mp (by decide +kernel))

def profile93_node91_cert : CutBound 5 := { lost := (rows 2 1 18 17 0), upper := (rows 29 30 13 14 19), lower := (rows 29 30 13 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 3 0 15 8 16), good := (rows 29 29 13 13 16) },{ target := 4, region := (rows 1 2 5 10 0), good := (rows 13 14 13 14 0) }] }

theorem profile93_node91 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,6] 2 profile93_node91_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9,6] 2 profile93_node91_cert).mp (by decide +kernel))

def profile93_node89_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node89 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9] 2 (by decide) (choices 2) [3,6] profile93_node89_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,9] (choices 2) [3,6] profile93_node89_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node90
  · exact profile93_node91

def profile93_node93_cert : CutBound 5 := { lost := (rows 2 1 17 0 10), upper := (rows 29 30 14 11 21), lower := (rows 29 30 14 11 16), losses := [{ target := 0, region := (rows 0 3 15 8 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 7 0 4 8 23), good := (rows 29 29 29 25 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 21 22 6 19 16) },{ target := 4, region := (rows 1 2 14 8 0), good := (rows 13 14 14 15 0) }] }

theorem profile93_node93 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,3] 2 profile93_node93_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,3] 2 profile93_node93_cert).mp (by decide +kernel))

def profile93_node94_cert : CutBound 5 := { lost := (rows 2 1 17 18 0), upper := (rows 29 30 14 13 19), lower := (rows 29 30 14 13 16), losses := [{ target := 0, region := (rows 0 3 15 8 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 3 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 4, region := (rows 1 2 6 9 0), good := (rows 13 14 14 13 0) }] }

theorem profile93_node94 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,5] 2 profile93_node94_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10,5] 2 profile93_node94_cert).mp (by decide +kernel))

def profile93_node92_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node92 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10] 2 (by decide) (choices 2) [3,5] profile93_node92_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28,10] (choices 2) [3,5] profile93_node92_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node93
  · exact profile93_node94

def profile93_node84_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node84 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28] 2 (by decide) (choices 2) [3,9,10] profile93_node84_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28,28] (choices 2) [3,9,10] profile93_node84_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node85
  · exact profile93_node89
  · exact profile93_node92

def profile93_node62_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile93_node62 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28] 2 (by decide) (choices 3) [13,21,28] profile93_node62_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [28] (choices 3) [13,21,28] profile93_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node63
  · exact profile93_node78
  · exact profile93_node84

def profile93_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile93_node0 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [] 2 (by decide) (choices 3) [14,22,28] profile93_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [] (choices 3) [14,22,28] profile93_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile93_node1
  · exact profile93_node39
  · exact profile93_node62

theorem profile93 : Upper (D (n:=5) [50,50,35,35,34]) (R (n:=5) [50,50,35,35,34]) [] 2 := profile93_node0

def profile94_node3_cert : CutBound 5 := { lost := (rows 16 16 0 1 1), upper := (rows 15 15 21 28 28), lower := (rows 15 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile94_node3 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,17] 2 profile94_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,17] 2 profile94_node3_cert).mp (by decide +kernel))

def profile94_node4_cert : CutBound 5 := { lost := (rows 16 16 0 0 8), upper := (rows 15 15 28 29 21), lower := (rows 15 15 28 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile94_node4 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,24] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,24] 2 profile94_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13,24] 2 profile94_node4_cert).mp (by decide +kernel))

def profile94_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node2 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13] 2 (by decide) (choices 2) [17,24] profile94_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,13] (choices 2) [17,24] profile94_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile94_node3
  · exact profile94_node4

def profile94_node6_cert : CutBound 5 := { lost := (rows 0 0 16 1 1), upper := (rows 15 23 13 28 28), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile94_node6 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,9] 2 profile94_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,9] 2 profile94_node6_cert).mp (by decide +kernel))

def profile94_node8_cert : CutBound 5 := { lost := (rows 16 0 1 16 1), upper := (rows 15 23 28 13 28), lower := (rows 15 23 28 13 16), losses := [{ target := 0, region := (rows 0 2 13 8 29), good := (rows 30 22 28 28 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 13 0) }] }

theorem profile94_node8 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24,5] 2 profile94_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24,5] 2 profile94_node8_cert).mp (by decide +kernel))

def profile94_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node7 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24] 2 (by decide) (choices 2) [5] profile94_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21,24] (choices 2) [5] profile94_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node8

def profile94_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node5 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21] 2 (by decide) (choices 2) [9,24] profile94_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,21] (choices 2) [9,24] profile94_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile94_node6
  · exact profile94_node7

def profile94_node10_cert : CutBound 5 := { lost := (rows 16 0 16 0 8), upper := (rows 15 30 13 29 21), lower := (rows 15 30 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 13 8 0) }] }

theorem profile94_node10 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,9] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,9] 2 profile94_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,9] 2 profile94_node10_cert).mp (by decide +kernel))

def profile94_node12_cert : CutBound 5 := { lost := (rows 16 1 0 16 1), upper := (rows 15 30 21 13 28), lower := (rows 15 30 21 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile94_node12 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17,5] 2 profile94_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17,5] 2 profile94_node12_cert).mp (by decide +kernel))

def profile94_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node11 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17] 2 (by decide) (choices 2) [5] profile94_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,17] (choices 2) [5] profile94_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node12

def profile94_node13_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 15 30 28 13 21), lower := (rows 15 30 28 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) }] }

theorem profile94_node13 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,24] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,24] 2 profile94_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28,24] 2 profile94_node13_cert).mp (by decide +kernel))

def profile94_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node9 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28] 2 (by decide) (choices 2) [9,17,24] profile94_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14,28] (choices 2) [9,17,24] profile94_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node10
  · exact profile94_node11
  · exact profile94_node13

def profile94_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node1 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile94_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [14] (choices 3) [13,21,28] profile94_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node2
  · exact profile94_node5
  · exact profile94_node9

def profile94_node16_cert : CutBound 5 := { lost := (rows 0 16 16 1 1), upper := (rows 23 15 13 28 28), lower := (rows 23 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile94_node16 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,9] 2 profile94_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,9] 2 profile94_node16_cert).mp (by decide +kernel))

def profile94_node18_cert : CutBound 5 := { lost := (rows 0 16 1 16 1), upper := (rows 23 15 28 13 28), lower := (rows 23 15 28 13 16), losses := [{ target := 0, region := (rows 0 2 14 8 30), good := (rows 22 30 28 28 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile94_node18 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24,5] 2 profile94_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24,5] 2 profile94_node18_cert).mp (by decide +kernel))

def profile94_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node17 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24] 2 (by decide) (choices 2) [5] profile94_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13,24] (choices 2) [5] profile94_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node18

def profile94_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node15 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13] 2 (by decide) (choices 2) [9,24] profile94_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,13] (choices 2) [9,24] profile94_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile94_node16
  · exact profile94_node17

def profile94_node19_cert : CutBound 5 := { lost := (rows 8 0 16 16 0), upper := (rows 23 30 13 13 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile94_node19 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,28] 2 profile94_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22,28] 2 profile94_node19_cert).mp (by decide +kernel))

def profile94_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node14 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22] 2 (by decide) (choices 3) [13,28] profile94_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [22] (choices 3) [13,28] profile94_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile94_node15
  · exact profile94_node19

def profile94_node22_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 29 15 7 28 28), lower := (rows 29 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 28 30 30 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 7 7 0 16) }] }

theorem profile94_node22 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,3] 2 profile94_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,3] 2 profile94_node22_cert).mp (by decide +kernel))

def profile94_node23_cert : CutBound 5 := { lost := (rows 0 0 0 1 9), upper := (rows 29 15 13 30 22), lower := (rows 29 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 12 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 5 0 16) }] }

theorem profile94_node23 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,9] 2 profile94_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,9] 2 profile94_node23_cert).mp (by decide +kernel))

def profile94_node24_cert : CutBound 5 := { lost := (rows 0 16 17 0 8), upper := (rows 29 15 14 29 21), lower := (rows 29 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 14 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 21 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile94_node24 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,10] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,10] 2 profile94_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,10] 2 profile94_node24_cert).mp (by decide +kernel))

def profile94_node25_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 29 15 21 14 30), lower := (rows 29 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 21 7 21 0 16) }] }

theorem profile94_node25 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,17] 2 profile94_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,17] 2 profile94_node25_cert).mp (by decide +kernel))

def profile94_node27_cert : CutBound 5 := { lost := (rows 0 16 1 16 1), upper := (rows 29 15 22 13 28), lower := (rows 29 15 22 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 27), good := (rows 28 30 22 28 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile94_node27 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18,5] 2 profile94_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18,5] 2 profile94_node27_cert).mp (by decide +kernel))

def profile94_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node26 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18] 2 (by decide) (choices 2) [5] profile94_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,18] (choices 2) [5] profile94_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node27

def profile94_node28_cert : CutBound 5 := { lost := (rows 0 16 1 16 8), upper := (rows 29 15 28 15 23), lower := (rows 29 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 28 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile94_node28 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,24] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,24] 2 profile94_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13,24] 2 profile94_node28_cert).mp (by decide +kernel))

def profile94_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node21 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile94_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,13] (choices 2) [3,9,10,17,18,24] profile94_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile94_node22
  · exact profile94_node23
  · exact profile94_node24
  · exact profile94_node25
  · exact profile94_node26
  · exact profile94_node28

def profile94_node29_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile94_node29 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,21] 2 profile94_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,21] 2 profile94_node29_cert).mp (by decide +kernel))

def profile94_node32_cert : CutBound 5 := { lost := (rows 0 1 0 16 1), upper := (rows 29 30 7 13 28), lower := (rows 29 30 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 13 0) }] }

theorem profile94_node32 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3,5] 2 profile94_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3,5] 2 profile94_node32_cert).mp (by decide +kernel))

def profile94_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node31 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3] 2 (by decide) (choices 2) [5] profile94_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,3] (choices 2) [5] profile94_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node32

def profile94_node34_cert : CutBound 5 := { lost := (rows 0 1 0 0 9), upper := (rows 29 30 13 13 22), lower := (rows 29 30 13 13 16), losses := [{ target := 0, region := (rows 0 15 4 8 31), good := (rows 30 30 30 30 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 22 5 5 16) }] }

theorem profile94_node34 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,5] 2 profile94_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,5] 2 profile94_node34_cert).mp (by decide +kernel))

def profile94_node35_cert : CutBound 5 := { lost := (rows 0 1 0 1 8), upper := (rows 29 30 13 14 21), lower := (rows 29 30 13 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 21 22 21 22 16) }] }

theorem profile94_node35 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,6] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,6] 2 profile94_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9,6] 2 profile94_node35_cert).mp (by decide +kernel))

def profile94_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node33 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9] 2 (by decide) (choices 2) [5,6] profile94_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,9] (choices 2) [5,6] profile94_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile94_node34
  · exact profile94_node35

def profile94_node36_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 29 30 14 13 21), lower := (rows 29 30 14 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 21 22 6 0 16) }] }

theorem profile94_node36 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,10] 2 :=
  cut_bound_sound (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,10] 2 profile94_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28,10] 2 profile94_node36_cert).mp (by decide +kernel))

def profile94_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node30 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28] 2 (by decide) (choices 2) [3,9,10] profile94_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28,28] (choices 2) [3,9,10] profile94_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node31
  · exact profile94_node33
  · exact profile94_node36

def profile94_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node20 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28] 2 (by decide) (choices 3) [13,21,28] profile94_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [28] (choices 3) [13,21,28] profile94_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node21
  · exact profile94_node29
  · exact profile94_node30

def profile94_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node0 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [] 2 (by decide) (choices 3) [14,22,28] profile94_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [] (choices 3) [14,22,28] profile94_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node1
  · exact profile94_node14
  · exact profile94_node20

theorem profile94 : Upper (D (n:=5) [50,49,36,35,34]) (R (n:=5) [50,49,36,35,34]) [] 2 := profile94_node0

def profile95_node4_cert : CutBound 5 := { lost := (rows 0 0 1 4 1), upper := (rows 15 23 28 25 28), lower := (rows 15 23 28 25 16), losses := [{ target := 0, region := (rows 0 2 13 8 29), good := (rows 30 22 28 28 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 24 25 16) }] }

theorem profile95_node4 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,17] 2 profile95_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,17] 2 profile95_node4_cert).mp (by decide +kernel))

def profile95_node5_cert : CutBound 5 := { lost := (rows 0 0 1 1 4), upper := (rows 15 23 28 28 25), lower := (rows 15 23 28 28 16), losses := [{ target := 0, region := (rows 0 2 30 30 16), good := (rows 14 30 28 28 28) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 24 24 16) }] }

theorem profile95_node5 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,20] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,20] 2 profile95_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24,20] 2 profile95_node5_cert).mp (by decide +kernel))

def profile95_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node3 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24] 2 (by decide) (choices 2) [17,20] profile95_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21,24] (choices 2) [17,20] profile95_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node4
  · exact profile95_node5

def profile95_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node2 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21] 2 (by decide) (choices 2) [24] profile95_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,21] (choices 2) [24] profile95_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile95_node3

def profile95_node8_cert : CutBound 5 := { lost := (rows 0 1 0 4 1), upper := (rows 15 30 21 25 28), lower := (rows 15 30 21 25 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 26 25 25 16) }] }

theorem profile95_node8 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,17] 2 profile95_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,17] 2 profile95_node8_cert).mp (by decide +kernel))

def profile95_node9_cert : CutBound 5 := { lost := (rows 0 1 0 1 4), upper := (rows 15 30 21 28 25), lower := (rows 15 30 21 28 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 14 30 30 30 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 17 24 16) }] }

theorem profile95_node9 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,20] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,20] 2 profile95_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17,20] 2 profile95_node9_cert).mp (by decide +kernel))

def profile95_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node7 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17] 2 (by decide) (choices 2) [17,20] profile95_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,17] (choices 2) [17,20] profile95_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node8
  · exact profile95_node9

def profile95_node10_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 15 30 28 29 21), lower := (rows 15 30 28 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) }] }

theorem profile95_node10 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,24] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,24] 2 profile95_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28,24] 2 profile95_node10_cert).mp (by decide +kernel))

def profile95_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node6 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28] 2 (by decide) (choices 2) [17,24] profile95_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14,28] (choices 2) [17,24] profile95_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node7
  · exact profile95_node10

def profile95_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile95_node1 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14] 2 (by decide) (choices 3) [21,28] profile95_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [14] (choices 3) [21,28] profile95_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node2
  · exact profile95_node6

def profile95_node13_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 29 15 21 30 30), lower := (rows 29 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 21 7 21 0 16) }] }

theorem profile95_node13 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,17] 2 profile95_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,17] 2 profile95_node13_cert).mp (by decide +kernel))

def profile95_node15_cert : CutBound 5 := { lost := (rows 0 0 1 4 1), upper := (rows 29 15 22 25 28), lower := (rows 29 15 22 25 16), losses := [{ target := 0, region := (rows 0 2 6 8 19), good := (rows 28 30 22 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 25 11 18 25 16) }] }

theorem profile95_node15 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,17] 2 profile95_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,17] 2 profile95_node15_cert).mp (by decide +kernel))

def profile95_node16_cert : CutBound 5 := { lost := (rows 0 16 0 1 4), upper := (rows 29 15 22 28 25), lower := (rows 29 15 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 28 14 30 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 25 27 18 24 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 6 12 0) }] }

theorem profile95_node16 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,20] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,20] 2 profile95_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18,20] 2 profile95_node16_cert).mp (by decide +kernel))

def profile95_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node14 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18] 2 (by decide) (choices 2) [17,20] profile95_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,18] (choices 2) [17,20] profile95_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node15
  · exact profile95_node16

def profile95_node17_cert : CutBound 5 := { lost := (rows 0 16 1 0 8), upper := (rows 29 15 28 31 23), lower := (rows 29 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 28 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 20 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 12 8 0) }] }

theorem profile95_node17 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,24] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,24] 2 profile95_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13,24] 2 profile95_node17_cert).mp (by decide +kernel))

def profile95_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node12 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13] 2 (by decide) (choices 2) [17,18,24] profile95_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,13] (choices 2) [17,18,24] profile95_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile95_node13
  · exact profile95_node14
  · exact profile95_node17

def profile95_node20_cert : CutBound 5 := { lost := (rows 0 1 0 4 1), upper := (rows 29 30 7 25 28), lower := (rows 29 30 7 25 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 25 26 11 25 16) }] }

theorem profile95_node20 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,17] 2 profile95_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,17] 2 profile95_node20_cert).mp (by decide +kernel))

def profile95_node21_cert : CutBound 5 := { lost := (rows 0 1 0 1 4), upper := (rows 29 30 7 28 25), lower := (rows 29 30 7 28 16), losses := [{ target := 0, region := (rows 0 11 4 11 16), good := (rows 30 30 14 30 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 25 26 19 24 16) }] }

theorem profile95_node21 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,20] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,20] 2 profile95_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3,20] 2 profile95_node21_cert).mp (by decide +kernel))

def profile95_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node19 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3] 2 (by decide) (choices 2) [17,20] profile95_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,3] (choices 2) [17,20] profile95_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node20
  · exact profile95_node21

def profile95_node23_cert : CutBound 5 := { lost := (rows 0 1 0 4 1), upper := (rows 29 30 13 25 22), lower := (rows 29 30 13 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 25 26 9 25 16) }] }

theorem profile95_node23 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,17] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,17] 2 profile95_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,17] 2 profile95_node23_cert).mp (by decide +kernel))

def profile95_node24_cert : CutBound 5 := { lost := (rows 0 1 0 5 0), upper := (rows 29 30 13 26 21), lower := (rows 29 30 13 26 16), losses := [{ target := 0, region := (rows 0 3 4 11 16), good := (rows 30 30 14 26 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 26 9 26 16) }] }

theorem profile95_node24 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,18] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,18] 2 profile95_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,18] 2 profile95_node24_cert).mp (by decide +kernel))

def profile95_node25_cert : CutBound 5 := { lost := (rows 0 1 16 1 0), upper := (rows 29 30 13 28 19), lower := (rows 29 30 13 28 16), losses := [{ target := 0, region := (rows 0 11 4 11 16), good := (rows 30 30 14 30 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 13 14 13 12 0) }] }

theorem profile95_node25 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,20] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,20] 2 profile95_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9,20] 2 profile95_node25_cert).mp (by decide +kernel))

def profile95_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node22 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9] 2 (by decide) (choices 2) [17,18,20] profile95_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,9] (choices 2) [17,18,20] profile95_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile95_node23
  · exact profile95_node24
  · exact profile95_node25

def profile95_node26_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 29 30 14 29 21), lower := (rows 29 30 14 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 21 22 6 0 16) }] }

theorem profile95_node26 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,10] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,10] 2 profile95_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,10] 2 profile95_node26_cert).mp (by decide +kernel))

def profile95_node28_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 29 30 28 11 21), lower := (rows 29 30 28 11 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 14 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 21 22 20 19 16) }] }

theorem profile95_node28 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,3] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,3] 2 profile95_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,3] 2 profile95_node28_cert).mp (by decide +kernel))

def profile95_node29_cert : CutBound 5 := { lost := (rows 0 1 1 16 0), upper := (rows 29 30 28 13 19), lower := (rows 29 30 28 13 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 14 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 13 14 12 13 0) }] }

theorem profile95_node29 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,5] 2 profile95_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24,5] 2 profile95_node29_cert).mp (by decide +kernel))

def profile95_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node27 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24] 2 (by decide) (choices 2) [3,5] profile95_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28,24] (choices 2) [3,5] profile95_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node28
  · exact profile95_node29

def profile95_node18_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile95_node18 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28] 2 (by decide) (choices 2) [3,9,10,24] profile95_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28,28] (choices 2) [3,9,10,24] profile95_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile95_node19
  · exact profile95_node22
  · exact profile95_node26
  · exact profile95_node27

def profile95_node11_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile95_node11 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28] 2 (by decide) (choices 3) [13,28] profile95_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [28] (choices 3) [13,28] profile95_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node12
  · exact profile95_node18

def profile95_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile95_node0 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [] 2 (by decide) (choices 3) [14,28] profile95_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [] (choices 3) [14,28] profile95_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node1
  · exact profile95_node11

theorem profile95 : Upper (D (n:=5) [50,49,35,35,35]) (R (n:=5) [50,49,35,35,35]) [] 2 := profile95_node0

#print axioms profile95
end Delivery.FiveVertexPositive12
