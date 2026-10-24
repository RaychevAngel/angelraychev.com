import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile67_node4_cert : CutBound 5 := { lost := (rows 0 0 8 6 9), upper := (rows 15 15 23 25 22), lower := (rows 15 15 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 22 24 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 25 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 27 25 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile67_node4 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,17] 2 profile67_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,17] 2 profile67_node4_cert).mp (by decide +kernel))

def profile67_node5_cert : CutBound 5 := { lost := (rows 0 0 8 5 10), upper := (rows 15 15 23 26 21), lower := (rows 15 15 23 26 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 30 26 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 21 24 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 27 26 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile67_node5 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,18] 2 profile67_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,18] 2 profile67_node5_cert).mp (by decide +kernel))

def profile67_node6_cert : CutBound 5 := { lost := (rows 0 0 8 3 12), upper := (rows 15 15 23 28 19), lower := (rows 15 15 23 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 30 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 28 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 19 24 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 20 16) }] }

theorem profile67_node6 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,20] 2 profile67_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19,20] 2 profile67_node6_cert).mp (by decide +kernel))

def profile67_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node3 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19] 2 (by decide) (choices 2) [17,18,20] profile67_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13,19] (choices 2) [17,18,20] profile67_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node4
  · exact profile67_node5
  · exact profile67_node6

def profile67_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node2 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13] 2 (by decide) (choices 3) [19] profile67_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,13] (choices 3) [19] profile67_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node3

def profile67_node9_cert : CutBound 5 := { lost := (rows 0 8 0 6 9), upper := (rows 15 23 15 25 22), lower := (rows 15 23 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 22 30 24 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 13 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 25 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 19 16) }] }

theorem profile67_node9 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,17] 2 profile67_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,17] 2 profile67_node9_cert).mp (by decide +kernel))

def profile67_node10_cert : CutBound 5 := { lost := (rows 0 8 0 5 10), upper := (rows 15 23 15 26 21), lower := (rows 15 23 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 26 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 26 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 18 16) }] }

theorem profile67_node10 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,18] 2 profile67_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,18] 2 profile67_node10_cert).mp (by decide +kernel))

def profile67_node11_cert : CutBound 5 := { lost := (rows 0 8 0 3 12), upper := (rows 15 23 15 28 19), lower := (rows 15 23 15 28 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 28 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 13 28 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 19 27 24 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile67_node11 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,20] 2 profile67_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11,20] 2 profile67_node11_cert).mp (by decide +kernel))

def profile67_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node8 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11] 2 (by decide) (choices 2) [17,18,20] profile67_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,11] (choices 2) [17,18,20] profile67_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node9
  · exact profile67_node10
  · exact profile67_node11

def profile67_node13_cert : CutBound 5 := { lost := (rows 0 8 8 4 3), upper := (rows 15 23 23 11 28), lower := (rows 15 23 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile67_node13 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,3] 2 profile67_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,3] 2 profile67_node13_cert).mp (by decide +kernel))

def profile67_node14_cert : CutBound 5 := { lost := (rows 0 8 8 2 5), upper := (rows 15 23 23 13 26), lower := (rows 15 23 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 25 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile67_node14 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,5] 2 profile67_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,5] 2 profile67_node14_cert).mp (by decide +kernel))

def profile67_node15_cert : CutBound 5 := { lost := (rows 0 8 8 1 6), upper := (rows 15 23 23 14 25), lower := (rows 15 23 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 30 30 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 10 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 6 16) }] }

theorem profile67_node15 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,6] 2 profile67_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19,6] 2 profile67_node15_cert).mp (by decide +kernel))

def profile67_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node12 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19] 2 (by decide) (choices 2) [3,5,6] profile67_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,19] (choices 2) [3,5,6] profile67_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node13
  · exact profile67_node14
  · exact profile67_node15

def profile67_node17_cert : CutBound 5 := { lost := (rows 16 8 0 20 9), upper := (rows 15 23 29 11 22), lower := (rows 15 23 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 22 28 26 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 25 11 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 19 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 11 0) }] }

theorem profile67_node17 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,3] 2 profile67_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,3] 2 profile67_node17_cert).mp (by decide +kernel))

def profile67_node18_cert : CutBound 5 := { lost := (rows 16 8 0 17 12), upper := (rows 15 23 29 14 19), lower := (rows 15 23 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 30 28 14 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 25 26 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 22 16) },{ target := 4, region := (rows 11 2 4 11 0), good := (rows 15 15 13 15 0) }] }

theorem profile67_node18 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,6] 2 profile67_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25,6] 2 profile67_node18_cert).mp (by decide +kernel))

def profile67_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node16 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25] 2 (by decide) (choices 2) [3,6] profile67_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,25] (choices 2) [3,6] profile67_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node17
  · exact profile67_node18

def profile67_node20_cert : CutBound 5 := { lost := (rows 16 8 0 20 10), upper := (rows 15 23 30 11 21), lower := (rows 15 23 30 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 21 28 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 26 11 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 19 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile67_node20 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,3] 2 profile67_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,3] 2 profile67_node20_cert).mp (by decide +kernel))

def profile67_node21_cert : CutBound 5 := { lost := (rows 16 8 0 18 12), upper := (rows 15 23 30 13 19), lower := (rows 15 23 30 13 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 29 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 26 25 16) },{ target := 3, region := (rows 1 11 4 0 27), good := (rows 23 23 22 23 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile67_node21 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,5] 2 profile67_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26,5] 2 profile67_node21_cert).mp (by decide +kernel))

def profile67_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node19 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26] 2 (by decide) (choices 2) [3,5] profile67_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21,26] (choices 2) [3,5] profile67_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node20
  · exact profile67_node21

def profile67_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node7 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21] 2 (by decide) (choices 3) [11,19,25,26] profile67_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,21] (choices 3) [11,19,25,26] profile67_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile67_node8
  · exact profile67_node12
  · exact profile67_node16
  · exact profile67_node19

def profile67_node24_cert : CutBound 5 := { lost := (rows 16 0 8 18 9), upper := (rows 15 27 23 13 22), lower := (rows 15 27 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 29 13 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 13 0) }] }

theorem profile67_node24 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,5] 2 profile67_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,5] 2 profile67_node24_cert).mp (by decide +kernel))

def profile67_node25_cert : CutBound 5 := { lost := (rows 16 0 8 17 10), upper := (rows 15 27 23 14 21), lower := (rows 15 27 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 30 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) },{ target := 4, region := (rows 13 2 4 13 0), good := (rows 15 11 15 15 0) }] }

theorem profile67_node25 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,6] 2 profile67_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19,6] 2 profile67_node25_cert).mp (by decide +kernel))

def profile67_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node23 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19] 2 (by decide) (choices 2) [5,6] profile67_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25,19] (choices 2) [5,6] profile67_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node24
  · exact profile67_node25

def profile67_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node22 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25] 2 (by decide) (choices 3) [19] profile67_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,25] (choices 3) [19] profile67_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node23

def profile67_node28_cert : CutBound 5 := { lost := (rows 16 0 8 20 10), upper := (rows 15 30 23 11 21), lower := (rows 15 30 23 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 21 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 11 26 27 11 16) },{ target := 3, region := (rows 1 2 13 0 29), good := (rows 23 22 23 23 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile67_node28 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,3] 2 profile67_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,3] 2 profile67_node28_cert).mp (by decide +kernel))

def profile67_node29_cert : CutBound 5 := { lost := (rows 16 0 8 18 12), upper := (rows 15 30 23 13 19), lower := (rows 15 30 23 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 29 13 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 19 25 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 21 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile67_node29 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,5] 2 profile67_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19,5] 2 profile67_node29_cert).mp (by decide +kernel))

def profile67_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node27 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19] 2 (by decide) (choices 2) [3,5] profile67_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28,19] (choices 2) [3,5] profile67_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node28
  · exact profile67_node29

def profile67_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node26 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28] 2 (by decide) (choices 3) [19] profile67_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14,28] (choices 3) [19] profile67_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node27

def profile67_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node1 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile67_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [14] (choices 3) [13,21,25,28] profile67_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile67_node2
  · exact profile67_node7
  · exact profile67_node22
  · exact profile67_node26

def profile67_node33_cert : CutBound 5 := { lost := (rows 0 16 8 18 9), upper := (rows 27 15 23 13 22), lower := (rows 27 15 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 22 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 29 13 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) },{ target := 4, region := (rows 1 14 4 14 0), good := (rows 11 15 15 15 0) }] }

theorem profile67_node33 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,5] 2 profile67_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,5] 2 profile67_node33_cert).mp (by decide +kernel))

def profile67_node34_cert : CutBound 5 := { lost := (rows 0 16 8 17 10), upper := (rows 27 15 23 14 21), lower := (rows 27 15 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 14 0) }] }

theorem profile67_node34 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,6] 2 profile67_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19,6] 2 profile67_node34_cert).mp (by decide +kernel))

def profile67_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node32 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19] 2 (by decide) (choices 2) [5,6] profile67_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13,19] (choices 2) [5,6] profile67_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node33
  · exact profile67_node34

def profile67_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node31 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13] 2 (by decide) (choices 3) [19] profile67_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,13] (choices 3) [19] profile67_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node32

def profile67_node35_cert : CutBound 5 := { lost := (rows 4 0 24 16 8), upper := (rows 27 30 7 15 23), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile67_node35 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,28] 2 profile67_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26,28] 2 profile67_node35_cert).mp (by decide +kernel))

def profile67_node30_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile67_node30 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26] 2 (by decide) (choices 3) [13,28] profile67_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [26] (choices 3) [13,28] profile67_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node31
  · exact profile67_node35

def profile67_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile67_node0 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [] 2 (by decide) (choices 3) [14,26] profile67_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [] (choices 3) [14,26] profile67_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node1
  · exact profile67_node30

theorem profile67 : Upper (D (n:=5) [51,51,51,34,34]) (R (n:=5) [51,51,51,34,34]) [] 2 := profile67_node0

def profile68_node3_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 31 15 13 29 21), lower := (rows 31 15 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile68_node3 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,9] 2 profile68_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,9] 2 profile68_node3_cert).mp (by decide +kernel))

def profile68_node4_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 31 15 21 13 29), lower := (rows 31 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile68_node4 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,17] 2 profile68_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13,17] 2 profile68_node4_cert).mp (by decide +kernel))

def profile68_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node2 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13] 2 (by decide) (choices 2) [9,17] profile68_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,13] (choices 2) [9,17] profile68_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node3
  · exact profile68_node4

def profile68_node5_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 13 13 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile68_node5 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,21] 2 profile68_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30,21] 2 profile68_node5_cert).mp (by decide +kernel))

def profile68_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile68_node1 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30] 2 (by decide) (choices 3) [13,21] profile68_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [30] (choices 3) [13,21] profile68_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node2
  · exact profile68_node5

def profile68_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node0 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [] 2 (by decide) (choices 4) [30] profile68_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [] (choices 4) [30] profile68_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node1

theorem profile68 : Upper (D (n:=5) [68,49,35,35,34]) (R (n:=5) [68,49,35,35,34]) [] 2 := profile68_node0

def profile69_node3_cert : CutBound 5 := { lost := (rows 0 16 24 2 2), upper := (rows 31 15 7 29 29), lower := (rows 31 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile69_node3 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,3] 2 profile69_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,3] 2 profile69_node3_cert).mp (by decide +kernel))

def profile69_node5_cert : CutBound 5 := { lost := (rows 0 0 2 6 9), upper := (rows 31 15 13 25 22), lower := (rows 31 15 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 24 16) },{ target := 1, region := (rows 1 0 15 9 16), good := (rows 29 13 13 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 9 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 17 16) }] }

theorem profile69_node5 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,17] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,17] 2 profile69_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,17] 2 profile69_node5_cert).mp (by decide +kernel))

def profile69_node6_cert : CutBound 5 := { lost := (rows 0 0 2 5 10), upper := (rows 31 15 13 26 21), lower := (rows 31 15 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 12 26 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 9 26 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 18 16) }] }

theorem profile69_node6 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,18] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,18] 2 profile69_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,18] 2 profile69_node6_cert).mp (by decide +kernel))

def profile69_node7_cert : CutBound 5 := { lost := (rows 0 0 2 3 12), upper := (rows 31 15 13 28 19), lower := (rows 31 15 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 12 28 16) },{ target := 1, region := (rows 1 0 7 9 16), good := (rows 29 13 13 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 25 24 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 20 16) }] }

theorem profile69_node7 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,20] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,20] 2 profile69_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9,20] 2 profile69_node7_cert).mp (by decide +kernel))

def profile69_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node4 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9] 2 (by decide) (choices 2) [17,18,20] profile69_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,9] (choices 2) [17,18,20] profile69_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node5
  · exact profile69_node6
  · exact profile69_node7

def profile69_node8_cert : CutBound 5 := { lost := (rows 0 16 17 2 10), upper := (rows 31 15 14 29 21), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile69_node8 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,10] 2 profile69_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,10] 2 profile69_node8_cert).mp (by decide +kernel))

def profile69_node10_cert : CutBound 5 := { lost := (rows 0 0 10 4 3), upper := (rows 31 15 21 11 28), lower := (rows 31 15 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 26 16) },{ target := 1, region := (rows 1 0 15 8 27), good := (rows 29 29 21 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 25 11 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 7 16) }] }

theorem profile69_node10 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,3] 2 profile69_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,3] 2 profile69_node10_cert).mp (by decide +kernel))

def profile69_node11_cert : CutBound 5 := { lost := (rows 0 0 10 2 5), upper := (rows 31 15 21 13 26), lower := (rows 31 15 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 28 16) },{ target := 1, region := (rows 1 0 5 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 5 16) }] }

theorem profile69_node11 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,5] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,5] 2 profile69_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,5] 2 profile69_node11_cert).mp (by decide +kernel))

def profile69_node12_cert : CutBound 5 := { lost := (rows 0 0 10 1 6), upper := (rows 31 15 21 14 25), lower := (rows 31 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 14 28 14 16) },{ target := 1, region := (rows 1 0 7 8 19), good := (rows 29 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 26 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 6 16) }] }

theorem profile69_node12 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,6] 2 profile69_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17,6] 2 profile69_node12_cert).mp (by decide +kernel))

def profile69_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node9 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17] 2 (by decide) (choices 2) [3,5,6] profile69_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,17] (choices 2) [3,5,6] profile69_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node10
  · exact profile69_node11
  · exact profile69_node12

def profile69_node13_cert : CutBound 5 := { lost := (rows 0 16 9 18 2), upper := (rows 31 15 22 13 29), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile69_node13 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,18] 2 profile69_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,18] 2 profile69_node13_cert).mp (by decide +kernel))

def profile69_node14_cert : CutBound 5 := { lost := (rows 0 16 3 16 8), upper := (rows 31 15 28 15 23), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile69_node14 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,24] 2 profile69_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13,24] 2 profile69_node14_cert).mp (by decide +kernel))

def profile69_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node2 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile69_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,13] (choices 2) [3,9,10,17,18,24] profile69_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile69_node3
  · exact profile69_node4
  · exact profile69_node8
  · exact profile69_node9
  · exact profile69_node13
  · exact profile69_node14

def profile69_node17_cert : CutBound 5 := { lost := (rows 0 8 2 4 3), upper := (rows 31 23 13 11 28), lower := (rows 31 23 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 28 26 16) },{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 21 29 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 27 9 11 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 3 16) }] }

theorem profile69_node17 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,3] 2 profile69_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,3] 2 profile69_node17_cert).mp (by decide +kernel))

def profile69_node18_cert : CutBound 5 := { lost := (rows 0 8 2 2 5), upper := (rows 31 23 13 13 26), lower := (rows 31 23 13 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 15 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 25 25 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 7 16) }] }

theorem profile69_node18 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,5] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,5] 2 profile69_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,5] 2 profile69_node18_cert).mp (by decide +kernel))

def profile69_node19_cert : CutBound 5 := { lost := (rows 0 8 2 1 6), upper := (rows 31 23 13 14 25), lower := (rows 31 23 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 30 12 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 21 29 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 25 26 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 6 16) }] }

theorem profile69_node19 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,6] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,6] 2 profile69_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9,6] 2 profile69_node19_cert).mp (by decide +kernel))

def profile69_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node16 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9] 2 (by decide) (choices 2) [3,5,6] profile69_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,9] (choices 2) [3,5,6] profile69_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node17
  · exact profile69_node18
  · exact profile69_node19

def profile69_node20_cert : CutBound 5 := { lost := (rows 0 8 17 18 2), upper := (rows 31 23 14 13 29), lower := (rows 31 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile69_node20 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,10] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,10] 2 profile69_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21,10] 2 profile69_node20_cert).mp (by decide +kernel))

def profile69_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node15 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21] 2 (by decide) (choices 2) [9,10] profile69_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,21] (choices 2) [9,10] profile69_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile69_node16
  · exact profile69_node20

def profile69_node22_cert : CutBound 5 := { lost := (rows 0 1 24 18 2), upper := (rows 31 30 7 13 29), lower := (rows 31 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile69_node22 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,3] 2 profile69_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,3] 2 profile69_node22_cert).mp (by decide +kernel))

def profile69_node23_cert : CutBound 5 := { lost := (rows 0 1 18 16 8), upper := (rows 31 30 13 15 23), lower := (rows 31 30 13 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 13 8 0) }] }

theorem profile69_node23 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,9] 2 profile69_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28,9] 2 profile69_node23_cert).mp (by decide +kernel))

def profile69_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node21 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28] 2 (by decide) (choices 2) [3,9] profile69_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30,28] (choices 2) [3,9] profile69_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile69_node22
  · exact profile69_node23

def profile69_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile69_node1 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile69_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [30] (choices 3) [13,21,28] profile69_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile69_node2
  · exact profile69_node15
  · exact profile69_node21

def profile69_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node0 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [] 2 (by decide) (choices 4) [30] profile69_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [] (choices 4) [30] profile69_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node1

theorem profile69 : Upper (D (n:=5) [67,50,35,35,34]) (R (n:=5) [67,50,35,35,34]) [] 2 := profile69_node0

def profile70_node3_cert : CutBound 5 := { lost := (rows 0 16 24 1 1), upper := (rows 31 15 7 30 30), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile70_node3 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,3] 2 profile70_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,3] 2 profile70_node3_cert).mp (by decide +kernel))

def profile70_node4_cert : CutBound 5 := { lost := (rows 0 16 18 1 9), upper := (rows 31 15 13 30 22), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile70_node4 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,9] 2 profile70_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,9] 2 profile70_node4_cert).mp (by decide +kernel))

def profile70_node6_cert : CutBound 5 := { lost := (rows 0 0 1 6 9), upper := (rows 31 15 14 25 22), lower := (rows 31 15 14 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 23), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 12 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 25 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 22 17 16) }] }

theorem profile70_node6 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,17] 2 profile70_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,17] 2 profile70_node6_cert).mp (by decide +kernel))

def profile70_node7_cert : CutBound 5 := { lost := (rows 0 0 1 5 10), upper := (rows 31 15 14 26 21), lower := (rows 31 15 14 26 16), losses := [{ target := 0, region := (rows 0 2 15 9 16), good := (rows 30 14 14 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 28 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 26 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 18 16) }] }

theorem profile70_node7 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,18] 2 profile70_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,18] 2 profile70_node7_cert).mp (by decide +kernel))

def profile70_node8_cert : CutBound 5 := { lost := (rows 0 0 1 3 12), upper := (rows 31 15 14 28 19), lower := (rows 31 15 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 12 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 26 24 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 20 16) }] }

theorem profile70_node8 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,20] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,20] 2 profile70_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10,20] 2 profile70_node8_cert).mp (by decide +kernel))

def profile70_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node5 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10] 2 (by decide) (choices 2) [17,18,20] profile70_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,10] (choices 2) [17,18,20] profile70_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node6
  · exact profile70_node7
  · exact profile70_node8

def profile70_node9_cert : CutBound 5 := { lost := (rows 0 16 10 17 1), upper := (rows 31 15 21 14 30), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile70_node9 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,17] 2 profile70_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,17] 2 profile70_node9_cert).mp (by decide +kernel))

def profile70_node11_cert : CutBound 5 := { lost := (rows 0 0 9 4 3), upper := (rows 31 15 22 11 28), lower := (rows 31 15 22 11 16), losses := [{ target := 0, region := (rows 0 2 15 8 27), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 20 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 26 11 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 7 16) }] }

theorem profile70_node11 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,3] 2 profile70_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,3] 2 profile70_node11_cert).mp (by decide +kernel))

def profile70_node12_cert : CutBound 5 := { lost := (rows 0 0 9 2 5), upper := (rows 31 15 22 13 26), lower := (rows 31 15 22 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 18 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 5 16) }] }

theorem profile70_node12 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,5] 2 profile70_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,5] 2 profile70_node12_cert).mp (by decide +kernel))

def profile70_node13_cert : CutBound 5 := { lost := (rows 0 0 9 1 6), upper := (rows 31 15 22 14 25), lower := (rows 31 15 22 14 16), losses := [{ target := 0, region := (rows 0 2 5 15 16), good := (rows 30 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 20 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 18 26 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 6 16) }] }

theorem profile70_node13 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,6] 2 profile70_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18,6] 2 profile70_node13_cert).mp (by decide +kernel))

def profile70_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node10 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18] 2 (by decide) (choices 2) [3,5,6] profile70_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,18] (choices 2) [3,5,6] profile70_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node11
  · exact profile70_node12
  · exact profile70_node13

def profile70_node14_cert : CutBound 5 := { lost := (rows 0 16 3 16 8), upper := (rows 31 15 28 15 23), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile70_node14 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,24] 2 profile70_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13,24] 2 profile70_node14_cert).mp (by decide +kernel))

def profile70_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node2 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile70_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,13] (choices 2) [3,9,10,17,18,24] profile70_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile70_node3
  · exact profile70_node4
  · exact profile70_node5
  · exact profile70_node9
  · exact profile70_node10
  · exact profile70_node14

def profile70_node16_cert : CutBound 5 := { lost := (rows 0 8 18 17 1), upper := (rows 31 23 13 14 30), lower := (rows 31 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile70_node16 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,9] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,9] 2 profile70_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,9] 2 profile70_node16_cert).mp (by decide +kernel))

def profile70_node18_cert : CutBound 5 := { lost := (rows 0 8 1 4 3), upper := (rows 31 23 14 11 28), lower := (rows 31 23 14 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 29), good := (rows 30 22 30 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 28 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 27 10 11 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 3 16) }] }

theorem profile70_node18 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,3] 2 profile70_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,3] 2 profile70_node18_cert).mp (by decide +kernel))

def profile70_node19_cert : CutBound 5 := { lost := (rows 0 8 1 2 5), upper := (rows 31 23 14 13 26), lower := (rows 31 23 14 13 16), losses := [{ target := 0, region := (rows 0 2 5 8 21), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 29 12 13 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 26 25 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 7 16) }] }

theorem profile70_node19 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,5] 2 profile70_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,5] 2 profile70_node19_cert).mp (by decide +kernel))

def profile70_node20_cert : CutBound 5 := { lost := (rows 0 8 1 1 6), upper := (rows 31 23 14 14 25), lower := (rows 31 23 14 14 16), losses := [{ target := 0, region := (rows 0 2 15 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 12 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 10 10 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 6 16) }] }

theorem profile70_node20 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,6] 2 profile70_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10,6] 2 profile70_node20_cert).mp (by decide +kernel))

def profile70_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node17 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10] 2 (by decide) (choices 2) [3,5,6] profile70_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21,10] (choices 2) [3,5,6] profile70_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node18
  · exact profile70_node19
  · exact profile70_node20

def profile70_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node15 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21] 2 (by decide) (choices 2) [9,10] profile70_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,21] (choices 2) [9,10] profile70_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile70_node16
  · exact profile70_node17

def profile70_node23_cert : CutBound 5 := { lost := (rows 0 1 8 4 3), upper := (rows 31 30 7 11 28), lower := (rows 31 30 7 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 28 21 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 26 11 11 16) },{ target := 3, region := (rows 1 2 13 0 16), good := (rows 23 22 7 7 16) }] }

theorem profile70_node23 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,3] 2 profile70_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,3] 2 profile70_node23_cert).mp (by decide +kernel))

def profile70_node24_cert : CutBound 5 := { lost := (rows 0 1 8 2 5), upper := (rows 31 30 7 13 26), lower := (rows 31 30 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 26 19 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 5 16) }] }

theorem profile70_node24 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,5] 2 profile70_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,5] 2 profile70_node24_cert).mp (by decide +kernel))

def profile70_node25_cert : CutBound 5 := { lost := (rows 0 1 8 1 6), upper := (rows 31 30 7 14 25), lower := (rows 31 30 7 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 28 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 19 10 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 6 16) }] }

theorem profile70_node25 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,6] 2 profile70_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3,6] 2 profile70_node25_cert).mp (by decide +kernel))

def profile70_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node22 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3] 2 (by decide) (choices 2) [3,5,6] profile70_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,3] (choices 2) [3,5,6] profile70_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node23
  · exact profile70_node24
  · exact profile70_node25

def profile70_node26_cert : CutBound 5 := { lost := (rows 0 1 18 16 8), upper := (rows 31 30 13 15 23), lower := (rows 31 30 13 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 13 8 0) }] }

theorem profile70_node26 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,9] 2 profile70_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,9] 2 profile70_node26_cert).mp (by decide +kernel))

def profile70_node27_cert : CutBound 5 := { lost := (rows 0 1 17 16 8), upper := (rows 31 30 14 15 23), lower := (rows 31 30 14 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 6 0 16) },{ target := 4, region := (rows 1 2 7 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile70_node27 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,10] 2 profile70_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28,10] 2 profile70_node27_cert).mp (by decide +kernel))

def profile70_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node21 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28] 2 (by decide) (choices 2) [3,9,10] profile70_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30,28] (choices 2) [3,9,10] profile70_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node22
  · exact profile70_node26
  · exact profile70_node27

def profile70_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile70_node1 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile70_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [30] (choices 3) [13,21,28] profile70_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile70_node2
  · exact profile70_node15
  · exact profile70_node21

def profile70_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node0 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [] 2 (by decide) (choices 4) [30] profile70_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [] (choices 4) [30] profile70_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node1

theorem profile70 : Upper (D (n:=5) [66,51,35,35,34]) (R (n:=5) [66,51,35,35,34]) [] 2 := profile70_node0

def profile71_node3_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 31 15 14 30 22), lower := (rows 31 15 14 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile71_node3 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,10] 2 profile71_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,10] 2 profile71_node3_cert).mp (by decide +kernel))

def profile71_node4_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 31 15 22 14 30), lower := (rows 31 15 22 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 15 0), good := (rows 15 15 14 8 0) }] }

theorem profile71_node4 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,18] 2 profile71_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13,18] 2 profile71_node4_cert).mp (by decide +kernel))

def profile71_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node2 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13] 2 (by decide) (choices 2) [10,18] profile71_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,13] (choices 2) [10,18] profile71_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile71_node3
  · exact profile71_node4

def profile71_node5_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 14 14 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile71_node5 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,21] 2 profile71_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,21] 2 profile71_node5_cert).mp (by decide +kernel))

def profile71_node6_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile71_node6 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,28] 2 profile71_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30,28] 2 profile71_node6_cert).mp (by decide +kernel))

def profile71_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile71_node1 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile71_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [30] (choices 3) [13,21,28] profile71_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile71_node2
  · exact profile71_node5
  · exact profile71_node6

def profile71_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node0 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [] 2 (by decide) (choices 4) [30] profile71_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [] (choices 4) [30] profile71_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node1

theorem profile71 : Upper (D (n:=5) [65,52,35,35,34]) (R (n:=5) [65,52,35,35,34]) [] 2 := profile71_node0

def profile72_node3_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 31 15 13 29 21), lower := (rows 31 15 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile72_node3 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,9] 2 profile72_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,9] 2 profile72_node3_cert).mp (by decide +kernel))

def profile72_node4_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 31 15 21 13 29), lower := (rows 31 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile72_node4 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,17] 2 profile72_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,17] 2 profile72_node4_cert).mp (by decide +kernel))

def profile72_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 28 13 21), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile72_node5 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,24] 2 profile72_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13,24] 2 profile72_node5_cert).mp (by decide +kernel))

def profile72_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node2 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13] 2 (by decide) (choices 2) [9,17,24] profile72_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,13] (choices 2) [9,17,24] profile72_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile72_node3
  · exact profile72_node4
  · exact profile72_node5

def profile72_node6_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 13 13 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile72_node6 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,21] 2 profile72_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,21] 2 profile72_node6_cert).mp (by decide +kernel))

def profile72_node7_cert : CutBound 5 := { lost := (rows 0 1 16 16 0), upper := (rows 31 30 13 13 29), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile72_node7 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,28] 2 profile72_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30,28] 2 profile72_node7_cert).mp (by decide +kernel))

def profile72_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node1 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile72_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [30] (choices 3) [13,21,28] profile72_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile72_node2
  · exact profile72_node6
  · exact profile72_node7

def profile72_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node0 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [] 2 (by decide) (choices 4) [30] profile72_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [] (choices 4) [30] profile72_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node1

theorem profile72 : Upper (D (n:=5) [67,49,36,35,34]) (R (n:=5) [67,49,36,35,34]) [] 2 := profile72_node0

def profile73_node3_cert : CutBound 5 := { lost := (rows 0 0 8 3 3), upper := (rows 31 15 7 28 28), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile73_node3 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,3] 2 profile73_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,3] 2 profile73_node3_cert).mp (by decide +kernel))

def profile73_node4_cert : CutBound 5 := { lost := (rows 0 16 18 1 9), upper := (rows 31 15 13 30 22), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile73_node4 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,9] 2 profile73_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,9] 2 profile73_node4_cert).mp (by decide +kernel))

def profile73_node5_cert : CutBound 5 := { lost := (rows 0 16 17 2 10), upper := (rows 31 15 14 29 21), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile73_node5 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,10] 2 profile73_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,10] 2 profile73_node5_cert).mp (by decide +kernel))

def profile73_node6_cert : CutBound 5 := { lost := (rows 0 16 10 17 1), upper := (rows 31 15 21 14 30), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile73_node6 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,17] 2 profile73_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,17] 2 profile73_node6_cert).mp (by decide +kernel))

def profile73_node7_cert : CutBound 5 := { lost := (rows 0 16 9 18 2), upper := (rows 31 15 22 13 29), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile73_node7 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,18] 2 profile73_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,18] 2 profile73_node7_cert).mp (by decide +kernel))

def profile73_node8_cert : CutBound 5 := { lost := (rows 0 16 3 16 8), upper := (rows 31 15 28 15 23), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile73_node8 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,24] 2 profile73_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13,24] 2 profile73_node8_cert).mp (by decide +kernel))

def profile73_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node2 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile73_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,13] (choices 2) [3,9,10,17,18,24] profile73_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile73_node3
  · exact profile73_node4
  · exact profile73_node5
  · exact profile73_node6
  · exact profile73_node7
  · exact profile73_node8

def profile73_node10_cert : CutBound 5 := { lost := (rows 0 8 18 17 1), upper := (rows 31 23 13 14 30), lower := (rows 31 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile73_node10 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,9] 2 profile73_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,9] 2 profile73_node10_cert).mp (by decide +kernel))

def profile73_node11_cert : CutBound 5 := { lost := (rows 0 8 17 18 2), upper := (rows 31 23 14 13 29), lower := (rows 31 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 6 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile73_node11 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,10] 2 profile73_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21,10] 2 profile73_node11_cert).mp (by decide +kernel))

def profile73_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node9 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21] 2 (by decide) (choices 2) [9,10] profile73_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,21] (choices 2) [9,10] profile73_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile73_node10
  · exact profile73_node11

def profile73_node13_cert : CutBound 5 := { lost := (rows 0 1 24 18 2), upper := (rows 31 30 7 13 29), lower := (rows 31 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile73_node13 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,3] 2 profile73_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,3] 2 profile73_node13_cert).mp (by decide +kernel))

def profile73_node14_cert : CutBound 5 := { lost := (rows 0 1 18 16 8), upper := (rows 31 30 13 15 23), lower := (rows 31 30 13 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 13 8 0) }] }

theorem profile73_node14 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,9] 2 profile73_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,9] 2 profile73_node14_cert).mp (by decide +kernel))

def profile73_node15_cert : CutBound 5 := { lost := (rows 0 1 1 2 10), upper := (rows 31 30 14 13 21), lower := (rows 31 30 14 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile73_node15 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,10] 2 profile73_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28,10] 2 profile73_node15_cert).mp (by decide +kernel))

def profile73_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node12 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28] 2 (by decide) (choices 2) [3,9,10] profile73_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30,28] (choices 2) [3,9,10] profile73_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node13
  · exact profile73_node14
  · exact profile73_node15

def profile73_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node1 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile73_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [30] (choices 3) [13,21,28] profile73_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node2
  · exact profile73_node9
  · exact profile73_node12

def profile73_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node0 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [] 2 (by decide) (choices 4) [30] profile73_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [] (choices 4) [30] profile73_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node1

theorem profile73 : Upper (D (n:=5) [66,50,36,35,34]) (R (n:=5) [66,50,36,35,34]) [] 2 := profile73_node0

def profile74_node3_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 31 15 14 30 22), lower := (rows 31 15 14 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile74_node3 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,10] 2 profile74_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,10] 2 profile74_node3_cert).mp (by decide +kernel))

def profile74_node4_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 31 15 22 14 30), lower := (rows 31 15 22 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 15 0), good := (rows 15 15 14 8 0) }] }

theorem profile74_node4 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,18] 2 profile74_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,18] 2 profile74_node4_cert).mp (by decide +kernel))

def profile74_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 28 14 22), lower := (rows 31 15 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile74_node5 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,24] 2 profile74_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13,24] 2 profile74_node5_cert).mp (by decide +kernel))

def profile74_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node2 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13] 2 (by decide) (choices 2) [10,18,24] profile74_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,13] (choices 2) [10,18,24] profile74_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile74_node3
  · exact profile74_node4
  · exact profile74_node5

def profile74_node6_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 14 14 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile74_node6 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,21] 2 profile74_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,21] 2 profile74_node6_cert).mp (by decide +kernel))

def profile74_node7_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile74_node7 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,28] 2 profile74_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30,28] 2 profile74_node7_cert).mp (by decide +kernel))

def profile74_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node1 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile74_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [30] (choices 3) [13,21,28] profile74_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile74_node2
  · exact profile74_node6
  · exact profile74_node7

def profile74_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node0 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [] 2 (by decide) (choices 4) [30] profile74_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [] (choices 4) [30] profile74_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node1

theorem profile74 : Upper (D (n:=5) [65,51,36,35,34]) (R (n:=5) [65,51,36,35,34]) [] 2 := profile74_node0

def profile75_node3_cert : CutBound 5 := { lost := (rows 16 0 16 0 8), upper := (rows 15 27 15 27 19), lower := (rows 15 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile75_node3 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,11] 2 profile75_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,11] 2 profile75_node3_cert).mp (by decide +kernel))

def profile75_node4_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 27 23 11 27), lower := (rows 15 27 23 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 5 2 4 15 0), good := (rows 15 11 15 8 0) }] }

theorem profile75_node4 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,19] 2 profile75_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,19] 2 profile75_node4_cert).mp (by decide +kernel))

def profile75_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 15 27 29 11 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 0 16) }] }

theorem profile75_node5 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,25] 2 profile75_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25,25] 2 profile75_node5_cert).mp (by decide +kernel))

def profile75_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node2 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25] 2 (by decide) (choices 3) [11,19,25] profile75_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14,25] (choices 3) [11,19,25] profile75_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node3
  · exact profile75_node4
  · exact profile75_node5

def profile75_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node1 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14] 2 (by decide) (choices 3) [25] profile75_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [14] (choices 3) [25] profile75_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node2

def profile75_node7_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 15 11 27), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile75_node7 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22,25] 2 profile75_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22,25] 2 profile75_node7_cert).mp (by decide +kernel))

def profile75_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node6 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22] 2 (by decide) (choices 3) [25] profile75_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [22] (choices 3) [25] profile75_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node7

def profile75_node10_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 27 15 15 27 19), lower := (rows 27 15 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile75_node10 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,11] 2 profile75_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,11] 2 profile75_node10_cert).mp (by decide +kernel))

def profile75_node11_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 27 15 23 11 27), lower := (rows 27 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 8 0) }] }

theorem profile75_node11 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,19] 2 profile75_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,19] 2 profile75_node11_cert).mp (by decide +kernel))

def profile75_node12_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 27 15 29 11 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 21 0 16) }] }

theorem profile75_node12 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,25] 2 profile75_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13,25] 2 profile75_node12_cert).mp (by decide +kernel))

def profile75_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node9 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13] 2 (by decide) (choices 3) [11,19,25] profile75_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,13] (choices 3) [11,19,25] profile75_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node10
  · exact profile75_node11
  · exact profile75_node12

def profile75_node13_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 15 11 27), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile75_node13 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,21] 2 profile75_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,21] 2 profile75_node13_cert).mp (by decide +kernel))

def profile75_node14_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile75_node14 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,25] 2 profile75_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26,25] 2 profile75_node14_cert).mp (by decide +kernel))

def profile75_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node8 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26] 2 (by decide) (choices 3) [13,21,25] profile75_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [26] (choices 3) [13,21,25] profile75_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node9
  · exact profile75_node13
  · exact profile75_node14

def profile75_node16_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile75_node16 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28,25] 2 profile75_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28,25] 2 profile75_node16_cert).mp (by decide +kernel))

def profile75_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node15 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28] 2 (by decide) (choices 3) [25] profile75_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [28] (choices 3) [25] profile75_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node16

def profile75_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node0 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [] 2 (by decide) (choices 3) [14,22,26,28] profile75_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [] (choices 3) [14,22,26,28] profile75_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile75_node1
  · exact profile75_node6
  · exact profile75_node8
  · exact profile75_node15

theorem profile75 : Upper (D (n:=5) [52,51,49,35,34]) (R (n:=5) [52,51,49,35,34]) [] 2 := profile75_node0

#print axioms profile75
end Delivery.FiveVertexPositive13
