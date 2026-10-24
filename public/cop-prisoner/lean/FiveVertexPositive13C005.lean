import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile82_node4_cert : CutBound 5 := { lost := (rows 0 0 2 6 5), upper := (rows 15 15 29 25 26), lower := (rows 15 15 29 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 24 16) },{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 13 29 29 16) },{ target := 2, region := (rows 1 2 0 15 19), good := (rows 27 27 25 25 16) }] }

theorem profile82_node4 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,17] 2 profile82_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,17] 2 profile82_node4_cert).mp (by decide +kernel))

def profile82_node5_cert : CutBound 5 := { lost := (rows 16 16 2 4 6), upper := (rows 15 15 29 26 25), lower := (rows 15 15 29 26 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 2 0 11 23), good := (rows 27 27 25 26 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 11 0) }] }

theorem profile82_node5 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,18] 2 profile82_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25,18] 2 profile82_node5_cert).mp (by decide +kernel))

def profile82_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node3 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25] 2 (by decide) (choices 2) [17,18] profile82_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,25] (choices 2) [17,18] profile82_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node4
  · exact profile82_node5

def profile82_node6_cert : CutBound 5 := { lost := (rows 16 16 0 6 6), upper := (rows 15 15 30 25 25), lower := (rows 15 15 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile82_node6 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,26] 2 profile82_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13,26] 2 profile82_node6_cert).mp (by decide +kernel))

def profile82_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node2 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13] 2 (by decide) (choices 3) [25,26] profile82_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,13] (choices 3) [25,26] profile82_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node3
  · exact profile82_node6

def profile82_node9_cert : CutBound 5 := { lost := (rows 0 4 0 6 3), upper := (rows 15 27 15 25 28), lower := (rows 15 27 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 24 16) },{ target := 1, region := (rows 1 0 4 15 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 11 27 16) }] }

theorem profile82_node9 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,17] 2 profile82_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,17] 2 profile82_node9_cert).mp (by decide +kernel))

def profile82_node10_cert : CutBound 5 := { lost := (rows 16 4 16 2 6), upper := (rows 15 27 15 28 25), lower := (rows 15 27 15 28 16), losses := [{ target := 1, region := (rows 1 0 4 13 23), good := (rows 29 25 29 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 13 0) }] }

theorem profile82_node10 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,20] 2 profile82_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11,20] 2 profile82_node10_cert).mp (by decide +kernel))

def profile82_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node8 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11] 2 (by decide) (choices 2) [17,20] profile82_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,11] (choices 2) [17,20] profile82_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node9
  · exact profile82_node10

def profile82_node12_cert : CutBound 5 := { lost := (rows 0 4 2 4 3), upper := (rows 15 27 29 11 28), lower := (rows 15 27 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) }] }

theorem profile82_node12 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,3] 2 profile82_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,3] 2 profile82_node12_cert).mp (by decide +kernel))

def profile82_node13_cert : CutBound 5 := { lost := (rows 0 4 2 2 5), upper := (rows 15 27 29 13 26), lower := (rows 15 27 29 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 6 15 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 15 0 8 31), good := (rows 27 27 27 27 16) }] }

theorem profile82_node13 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,5] 2 profile82_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,5] 2 profile82_node13_cert).mp (by decide +kernel))

def profile82_node14_cert : CutBound 5 := { lost := (rows 0 4 2 1 6), upper := (rows 15 27 29 14 25), lower := (rows 15 27 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 28 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) }] }

theorem profile82_node14 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,6] 2 profile82_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25,6] 2 profile82_node14_cert).mp (by decide +kernel))

def profile82_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node11 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25] 2 (by decide) (choices 2) [3,5,6] profile82_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,25] (choices 2) [3,5,6] profile82_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node12
  · exact profile82_node13
  · exact profile82_node14

def profile82_node15_cert : CutBound 5 := { lost := (rows 16 0 1 18 2), upper := (rows 15 27 30 13 29), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile82_node15 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,26] 2 profile82_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25,26] 2 profile82_node15_cert).mp (by decide +kernel))

def profile82_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node7 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25] 2 (by decide) (choices 3) [11,25,26] profile82_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,25] (choices 3) [11,25,26] profile82_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node8
  · exact profile82_node11
  · exact profile82_node15

def profile82_node17_cert : CutBound 5 := { lost := (rows 16 0 16 6 6), upper := (rows 15 30 15 25 25), lower := (rows 15 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile82_node17 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,11] 2 profile82_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,11] 2 profile82_node17_cert).mp (by decide +kernel))

def profile82_node18_cert : CutBound 5 := { lost := (rows 16 1 0 20 4), upper := (rows 15 30 29 11 27), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile82_node18 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,25] 2 profile82_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28,25] 2 profile82_node18_cert).mp (by decide +kernel))

def profile82_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node16 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28] 2 (by decide) (choices 3) [11,25] profile82_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14,28] (choices 3) [11,25] profile82_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node17
  · exact profile82_node18

def profile82_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node1 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14] 2 (by decide) (choices 3) [13,25,28] profile82_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [14] (choices 3) [13,25,28] profile82_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node2
  · exact profile82_node7
  · exact profile82_node16

def profile82_node22_cert : CutBound 5 := { lost := (rows 0 16 16 6 3), upper := (rows 27 15 15 25 28), lower := (rows 27 15 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 30 24 16) },{ target := 1, region := (rows 1 0 4 15 22), good := (rows 25 29 29 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 25 16) },{ target := 4, region := (rows 1 15 15 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile82_node22 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,17] 2 profile82_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,17] 2 profile82_node22_cert).mp (by decide +kernel))

def profile82_node23_cert : CutBound 5 := { lost := (rows 4 16 16 2 6), upper := (rows 27 15 15 28 25), lower := (rows 27 15 15 28 16), losses := [{ target := 1, region := (rows 1 0 4 14 23), good := (rows 25 29 29 28 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 27 27 27 25 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 14 0) }] }

theorem profile82_node23 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,20] 2 profile82_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11,20] 2 profile82_node23_cert).mp (by decide +kernel))

def profile82_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node21 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11] 2 (by decide) (choices 2) [17,20] profile82_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,11] (choices 2) [17,20] profile82_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node22
  · exact profile82_node23

def profile82_node25_cert : CutBound 5 := { lost := (rows 0 16 2 20 3), upper := (rows 27 15 29 11 28), lower := (rows 27 15 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 28 26 16) },{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 25 11 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 11 0) }] }

theorem profile82_node25 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,3] 2 profile82_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,3] 2 profile82_node25_cert).mp (by decide +kernel))

def profile82_node26_cert : CutBound 5 := { lost := (rows 4 0 2 2 5), upper := (rows 27 15 29 13 26), lower := (rows 27 15 29 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 26 30 28 28 16) },{ target := 1, region := (rows 1 0 5 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 25 16) }] }

theorem profile82_node26 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,5] 2 profile82_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,5] 2 profile82_node26_cert).mp (by decide +kernel))

def profile82_node27_cert : CutBound 5 := { lost := (rows 4 0 2 1 6), upper := (rows 27 15 29 14 25), lower := (rows 27 15 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 26 14 28 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 11 2 0 8 31), good := (rows 27 27 25 27 16) }] }

theorem profile82_node27 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,6] 2 profile82_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25,6] 2 profile82_node27_cert).mp (by decide +kernel))

def profile82_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node24 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25] 2 (by decide) (choices 2) [3,5,6] profile82_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,25] (choices 2) [3,5,6] profile82_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node25
  · exact profile82_node26
  · exact profile82_node27

def profile82_node28_cert : CutBound 5 := { lost := (rows 4 0 1 18 2), upper := (rows 27 15 30 13 29), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 11 27 8 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 14 8 0) }] }

theorem profile82_node28 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,26] 2 profile82_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13,26] 2 profile82_node28_cert).mp (by decide +kernel))

def profile82_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node20 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13] 2 (by decide) (choices 3) [11,25,26] profile82_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,13] (choices 3) [11,25,26] profile82_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node21
  · exact profile82_node24
  · exact profile82_node28

def profile82_node30_cert : CutBound 5 := { lost := (rows 4 4 16 18 2), upper := (rows 27 27 15 13 29), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile82_node30 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25,11] 2 profile82_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25,11] 2 profile82_node30_cert).mp (by decide +kernel))

def profile82_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node29 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25] 2 (by decide) (choices 3) [11] profile82_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,25] (choices 3) [11] profile82_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile82_node30

def profile82_node32_cert : CutBound 5 := { lost := (rows 4 0 16 18 2), upper := (rows 27 30 15 13 29), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile82_node32 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28,11] 2 profile82_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28,11] 2 profile82_node32_cert).mp (by decide +kernel))

def profile82_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node31 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28] 2 (by decide) (choices 3) [11] profile82_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26,28] (choices 3) [11] profile82_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile82_node32

def profile82_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node19 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26] 2 (by decide) (choices 3) [13,25,28] profile82_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [26] (choices 3) [13,25,28] profile82_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile82_node20
  · exact profile82_node29
  · exact profile82_node31

def profile82_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile82_node0 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [] 2 (by decide) (choices 3) [14,26] profile82_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [] (choices 3) [14,26] profile82_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node1
  · exact profile82_node19

theorem profile82 : Upper (D (n:=5) [51,50,50,36,34]) (R (n:=5) [51,50,50,36,34]) [] 2 := profile82_node0

def profile83_node3_cert : CutBound 5 := { lost := (rows 0 16 8 0 0), upper := (rows 31 15 21 29 29), lower := (rows 31 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile83_node3 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,17] 2 profile83_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,17] 2 profile83_node3_cert).mp (by decide +kernel))

def profile83_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 28 29 21), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile83_node4 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,24] 2 profile83_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13,24] 2 profile83_node4_cert).mp (by decide +kernel))

def profile83_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node2 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13] 2 (by decide) (choices 2) [17,24] profile83_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,13] (choices 2) [17,24] profile83_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile83_node3
  · exact profile83_node4

def profile83_node6_cert : CutBound 5 := { lost := (rows 0 1 0 0 8), upper := (rows 31 30 13 29 21), lower := (rows 31 30 13 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 21 0 16) }] }

theorem profile83_node6 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28,9] 2 profile83_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28,9] 2 profile83_node6_cert).mp (by decide +kernel))

def profile83_node5_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile83_node5 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28] 2 (by decide) (choices 2) [9] profile83_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30,28] (choices 2) [9] profile83_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node6

def profile83_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile83_node1 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30] 2 (by decide) (choices 3) [13,28] profile83_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [30] (choices 3) [13,28] profile83_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile83_node2
  · exact profile83_node5

def profile83_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node0 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [] 2 (by decide) (choices 4) [30] profile83_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [] (choices 4) [30] profile83_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node1

theorem profile83 : Upper (D (n:=5) [67,49,35,35,35]) (R (n:=5) [67,49,35,35,35]) [] 2 := profile83_node0

def profile84_node3_cert : CutBound 5 := { lost := (rows 0 16 10 1 1), upper := (rows 31 15 21 30 30), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile84_node3 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,17] 2 profile84_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,17] 2 profile84_node3_cert).mp (by decide +kernel))

def profile84_node4_cert : CutBound 5 := { lost := (rows 0 16 9 2 2), upper := (rows 31 15 22 29 29), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 6 8 0) }] }

theorem profile84_node4 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,18] 2 profile84_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,18] 2 profile84_node4_cert).mp (by decide +kernel))

def profile84_node6_cert : CutBound 5 := { lost := (rows 0 0 3 6 1), upper := (rows 31 15 28 25 22), lower := (rows 31 15 28 25 16), losses := [{ target := 0, region := (rows 0 2 15 8 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 13 9 16), good := (rows 29 13 28 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 24 25 16) }] }

theorem profile84_node6 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,17] 2 profile84_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,17] 2 profile84_node6_cert).mp (by decide +kernel))

def profile84_node7_cert : CutBound 5 := { lost := (rows 0 0 3 5 2), upper := (rows 31 15 28 26 21), lower := (rows 31 15 28 26 16), losses := [{ target := 0, region := (rows 0 2 13 9 16), good := (rows 30 14 28 30 16) },{ target := 1, region := (rows 1 0 15 8 19), good := (rows 29 29 28 28 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 24 26 16) }] }

theorem profile84_node7 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,18] 2 profile84_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,18] 2 profile84_node7_cert).mp (by decide +kernel))

def profile84_node8_cert : CutBound 5 := { lost := (rows 0 0 3 3 4), upper := (rows 31 15 28 28 19), lower := (rows 31 15 28 28 16), losses := [{ target := 0, region := (rows 0 2 29 29 16), good := (rows 30 14 28 28 28) },{ target := 1, region := (rows 1 0 29 29 16), good := (rows 29 13 28 28 28) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 24 24 16) }] }

theorem profile84_node8 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,20] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,20] 2 profile84_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24,20] 2 profile84_node8_cert).mp (by decide +kernel))

def profile84_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node5 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24] 2 (by decide) (choices 2) [17,18,20] profile84_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13,24] (choices 2) [17,18,20] profile84_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile84_node6
  · exact profile84_node7
  · exact profile84_node8

def profile84_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node2 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13] 2 (by decide) (choices 2) [17,18,24] profile84_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,13] (choices 2) [17,18,24] profile84_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile84_node3
  · exact profile84_node4
  · exact profile84_node5

def profile84_node10_cert : CutBound 5 := { lost := (rows 0 1 24 2 2), upper := (rows 31 30 7 29 29), lower := (rows 31 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile84_node10 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,3] 2 profile84_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,3] 2 profile84_node10_cert).mp (by decide +kernel))

def profile84_node12_cert : CutBound 5 := { lost := (rows 0 1 2 6 1), upper := (rows 31 30 13 25 22), lower := (rows 31 30 13 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 1 0 13 9 16), good := (rows 29 28 13 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 26 9 25 16) }] }

theorem profile84_node12 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,17] 2 profile84_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,17] 2 profile84_node12_cert).mp (by decide +kernel))

def profile84_node13_cert : CutBound 5 := { lost := (rows 0 1 2 5 2), upper := (rows 31 30 13 26 21), lower := (rows 31 30 13 26 16), losses := [{ target := 0, region := (rows 0 3 4 11 16), good := (rows 30 30 14 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 29 24 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 26 9 26 16) }] }

theorem profile84_node13 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,18] 2 profile84_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,18] 2 profile84_node13_cert).mp (by decide +kernel))

def profile84_node14_cert : CutBound 5 := { lost := (rows 0 1 2 3 4), upper := (rows 31 30 13 28 19), lower := (rows 31 30 13 28 16), losses := [{ target := 0, region := (rows 0 11 4 11 16), good := (rows 30 30 14 30 16) },{ target := 1, region := (rows 1 0 5 11 16), good := (rows 29 28 13 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 25 24 16) }] }

theorem profile84_node14 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,20] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,20] 2 profile84_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9,20] 2 profile84_node14_cert).mp (by decide +kernel))

def profile84_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node11 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9] 2 (by decide) (choices 2) [17,18,20] profile84_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,9] (choices 2) [17,18,20] profile84_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile84_node12
  · exact profile84_node13
  · exact profile84_node14

def profile84_node15_cert : CutBound 5 := { lost := (rows 0 1 1 2 10), upper := (rows 31 30 14 29 21), lower := (rows 31 30 14 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile84_node15 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,10] 2 profile84_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,10] 2 profile84_node15_cert).mp (by decide +kernel))

def profile84_node16_cert : CutBound 5 := { lost := (rows 0 1 3 16 8), upper := (rows 31 30 28 15 23), lower := (rows 31 30 28 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 28 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 14 12 8 0) }] }

theorem profile84_node16 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,24] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,24] 2 profile84_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28,24] 2 profile84_node16_cert).mp (by decide +kernel))

def profile84_node9_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile84_node9 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28] 2 (by decide) (choices 2) [3,9,10,24] profile84_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30,28] (choices 2) [3,9,10,24] profile84_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile84_node10
  · exact profile84_node11
  · exact profile84_node15
  · exact profile84_node16

def profile84_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile84_node1 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30] 2 (by decide) (choices 3) [13,28] profile84_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [30] (choices 3) [13,28] profile84_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node2
  · exact profile84_node9

def profile84_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node0 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [] 2 (by decide) (choices 4) [30] profile84_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [] (choices 4) [30] profile84_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node1

theorem profile84 : Upper (D (n:=5) [66,50,35,35,35]) (R (n:=5) [66,50,35,35,35]) [] 2 := profile84_node0

def profile85_node3_cert : CutBound 5 := { lost := (rows 0 16 8 0 0), upper := (rows 31 15 22 30 30), lower := (rows 31 15 22 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 6 8 0) }] }

theorem profile85_node3 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,18] 2 profile85_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,18] 2 profile85_node3_cert).mp (by decide +kernel))

def profile85_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 28 30 22), lower := (rows 31 15 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile85_node4 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,24] 2 profile85_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13,24] 2 profile85_node4_cert).mp (by decide +kernel))

def profile85_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node2 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13] 2 (by decide) (choices 2) [18,24] profile85_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,13] (choices 2) [18,24] profile85_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile85_node3
  · exact profile85_node4

def profile85_node6_cert : CutBound 5 := { lost := (rows 0 0 24 0 0), upper := (rows 31 30 7 30 30), lower := (rows 31 30 7 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 7 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile85_node6 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,3] 2 profile85_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,3] 2 profile85_node6_cert).mp (by decide +kernel))

def profile85_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 30 13 30 22), lower := (rows 31 30 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 22 21 0 16) }] }

theorem profile85_node7 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,9] 2 profile85_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,9] 2 profile85_node7_cert).mp (by decide +kernel))

def profile85_node8_cert : CutBound 5 := { lost := (rows 0 0 16 0 8), upper := (rows 31 30 14 31 23), lower := (rows 31 30 14 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 6 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 14 14 8 0) }] }

theorem profile85_node8 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,10] 2 profile85_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,10] 2 profile85_node8_cert).mp (by decide +kernel))

def profile85_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 30 28 15 23), lower := (rows 31 30 28 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 28 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) }] }

theorem profile85_node9 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,24] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,24] 2 profile85_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28,24] 2 profile85_node9_cert).mp (by decide +kernel))

def profile85_node5_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile85_node5 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28] 2 (by decide) (choices 2) [3,9,10,24] profile85_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30,28] (choices 2) [3,9,10,24] profile85_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile85_node6
  · exact profile85_node7
  · exact profile85_node8
  · exact profile85_node9

def profile85_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile85_node1 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30] 2 (by decide) (choices 3) [13,28] profile85_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [30] (choices 3) [13,28] profile85_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile85_node2
  · exact profile85_node5

def profile85_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node0 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [] 2 (by decide) (choices 4) [30] profile85_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [] (choices 4) [30] profile85_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node1

theorem profile85 : Upper (D (n:=5) [65,51,35,35,35]) (R (n:=5) [65,51,35,35,35]) [] 2 := profile85_node0

def profile86_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 21 28 28), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile86_node3 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,17] 2 profile86_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,17] 2 profile86_node3_cert).mp (by decide +kernel))

def profile86_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 28 29 21), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile86_node4 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,24] 2 profile86_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13,24] 2 profile86_node4_cert).mp (by decide +kernel))

def profile86_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node2 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13] 2 (by decide) (choices 2) [17,24] profile86_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,13] (choices 2) [17,24] profile86_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile86_node3
  · exact profile86_node4

def profile86_node6_cert : CutBound 5 := { lost := (rows 0 1 0 0 8), upper := (rows 31 30 13 29 21), lower := (rows 31 30 13 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 21 0 16) }] }

theorem profile86_node6 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,9] 2 profile86_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,9] 2 profile86_node6_cert).mp (by decide +kernel))

def profile86_node7_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 31 30 28 13 21), lower := (rows 31 30 28 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile86_node7 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,24] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,24] 2 profile86_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28,24] 2 profile86_node7_cert).mp (by decide +kernel))

def profile86_node5_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile86_node5 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28] 2 (by decide) (choices 2) [9,24] profile86_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30,28] (choices 2) [9,24] profile86_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile86_node6
  · exact profile86_node7

def profile86_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile86_node1 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30] 2 (by decide) (choices 3) [13,28] profile86_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [30] (choices 3) [13,28] profile86_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile86_node2
  · exact profile86_node5

def profile86_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node0 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [] 2 (by decide) (choices 4) [30] profile86_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [] (choices 4) [30] profile86_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node1

theorem profile86 : Upper (D (n:=5) [66,49,36,35,35]) (R (n:=5) [66,49,36,35,35]) [] 2 := profile86_node0

def profile87_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 15 22 28 28), lower := (rows 31 15 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 28 8 16) }] }

theorem profile87_node3 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,18] 2 profile87_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,18] 2 profile87_node3_cert).mp (by decide +kernel))

def profile87_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 28 30 22), lower := (rows 31 15 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile87_node4 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,24] 2 profile87_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13,24] 2 profile87_node4_cert).mp (by decide +kernel))

def profile87_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node2 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13] 2 (by decide) (choices 2) [18,24] profile87_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,13] (choices 2) [18,24] profile87_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile87_node3
  · exact profile87_node4

def profile87_node6_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 30 7 28 28), lower := (rows 31 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 28 29 8 16) }] }

theorem profile87_node6 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,3] 2 profile87_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,3] 2 profile87_node6_cert).mp (by decide +kernel))

def profile87_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 30 13 30 22), lower := (rows 31 30 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 22 21 0 16) }] }

theorem profile87_node7 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,9] 2 profile87_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,9] 2 profile87_node7_cert).mp (by decide +kernel))

def profile87_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 30 14 29 21), lower := (rows 31 30 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) }] }

theorem profile87_node8 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,10] 2 profile87_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,10] 2 profile87_node8_cert).mp (by decide +kernel))

def profile87_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 30 28 15 23), lower := (rows 31 30 28 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 28 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 20 0 16) }] }

theorem profile87_node9 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,24] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,24] 2 profile87_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28,24] 2 profile87_node9_cert).mp (by decide +kernel))

def profile87_node5_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile87_node5 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28] 2 (by decide) (choices 2) [3,9,10,24] profile87_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30,28] (choices 2) [3,9,10,24] profile87_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile87_node6
  · exact profile87_node7
  · exact profile87_node8
  · exact profile87_node9

def profile87_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile87_node1 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30] 2 (by decide) (choices 3) [13,28] profile87_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [30] (choices 3) [13,28] profile87_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile87_node2
  · exact profile87_node5

def profile87_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node0 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [] 2 (by decide) (choices 4) [30] profile87_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [] (choices 4) [30] profile87_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node1

theorem profile87 : Upper (D (n:=5) [65,50,36,35,35]) (R (n:=5) [65,50,36,35,35]) [] 2 := profile87_node0

def profile88_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 15 27 23 25 25), lower := (rows 15 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile88_node3 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,19] 2 profile88_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,19] 2 profile88_node3_cert).mp (by decide +kernel))

def profile88_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 15 27 29 27 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 0 16) }] }

theorem profile88_node4 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,25] 2 profile88_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25,25] 2 profile88_node4_cert).mp (by decide +kernel))

def profile88_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node2 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25] 2 (by decide) (choices 3) [19,25] profile88_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14,25] (choices 3) [19,25] profile88_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node3
  · exact profile88_node4

def profile88_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node1 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14] 2 (by decide) (choices 3) [25] profile88_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [14] (choices 3) [25] profile88_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node2

def profile88_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 15 23 25 25), lower := (rows 27 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile88_node7 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,19] 2 profile88_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,19] 2 profile88_node7_cert).mp (by decide +kernel))

def profile88_node8_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 27 15 29 27 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 21 0 16) }] }

theorem profile88_node8 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,25] 2 profile88_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13,25] 2 profile88_node8_cert).mp (by decide +kernel))

def profile88_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node6 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13] 2 (by decide) (choices 3) [19,25] profile88_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,13] (choices 3) [19,25] profile88_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node7
  · exact profile88_node8

def profile88_node10_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 27 15 29 21), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) }] }

theorem profile88_node10 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,11] 2 profile88_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,11] 2 profile88_node10_cert).mp (by decide +kernel))

def profile88_node12_cert : CutBound 5 := { lost := (rows 0 0 2 0 2), upper := (rows 27 27 29 11 21), lower := (rows 27 27 29 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) }] }

theorem profile88_node12 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,3] 2 profile88_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,3] 2 profile88_node12_cert).mp (by decide +kernel))

def profile88_node13_cert : CutBound 5 := { lost := (rows 0 0 2 2 0), upper := (rows 27 27 29 13 19), lower := (rows 27 27 29 13 16), losses := [{ target := 1, region := (rows 1 0 7 15 16), good := (rows 29 29 29 13 16) }] }

theorem profile88_node13 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,5] 2 profile88_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25,5] 2 profile88_node13_cert).mp (by decide +kernel))

def profile88_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node11 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25] 2 (by decide) (choices 2) [3,5] profile88_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25,25] (choices 2) [3,5] profile88_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node12
  · exact profile88_node13

def profile88_node9_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node9 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25] 2 (by decide) (choices 3) [11,25] profile88_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26,25] (choices 3) [11,25] profile88_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node10
  · exact profile88_node11

def profile88_node5_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node5 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26] 2 (by decide) (choices 3) [13,25] profile88_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [26] (choices 3) [13,25] profile88_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node6
  · exact profile88_node9

def profile88_node16_cert : CutBound 5 := { lost := (rows 0 0 16 0 8), upper := (rows 29 27 15 27 19), lower := (rows 29 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 13 15 15 8 0) }] }

theorem profile88_node16 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,11] 2 profile88_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,11] 2 profile88_node16_cert).mp (by decide +kernel))

def profile88_node17_cert : CutBound 5 := { lost := (rows 2 0 2 0 0), upper := (rows 29 27 29 11 19), lower := (rows 29 27 29 8 16), losses := [{ target := 1, region := (rows 7 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile88_node17 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,25] 2 profile88_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25,25] 2 profile88_node17_cert).mp (by decide +kernel))

def profile88_node15_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node15 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25] 2 (by decide) (choices 3) [11,25] profile88_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28,25] (choices 3) [11,25] profile88_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node16
  · exact profile88_node17

def profile88_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node14 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28] 2 (by decide) (choices 3) [25] profile88_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [28] (choices 3) [25] profile88_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node15

def profile88_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node0 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [] 2 (by decide) (choices 3) [14,26,28] profile88_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [] (choices 3) [14,26,28] profile88_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node1
  · exact profile88_node5
  · exact profile88_node14

theorem profile88 : Upper (D (n:=5) [52,50,49,35,35]) (R (n:=5) [52,50,49,35,35]) [] 2 := profile88_node0

def profile89_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 15 27 23 25 26), lower := (rows 15 27 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 26 22 24 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 13 25 29 25 16) }] }

theorem profile89_node4 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,17] 2 profile89_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,17] 2 profile89_node4_cert).mp (by decide +kernel))

def profile89_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 15 27 23 26 25), lower := (rows 15 27 23 26 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 14 26 30 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 25 21 24 16) }] }

theorem profile89_node5 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,18] 2 profile89_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19,18] 2 profile89_node5_cert).mp (by decide +kernel))

def profile89_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node3 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19] 2 (by decide) (choices 2) [17,18] profile89_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,19] (choices 2) [17,18] profile89_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node4
  · exact profile89_node5

def profile89_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 15 27 29 27 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 0 16) }] }

theorem profile89_node6 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,25] 2 profile89_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,25] 2 profile89_node6_cert).mp (by decide +kernel))

def profile89_node7_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 15 27 30 27 19), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 22 0 16) }] }

theorem profile89_node7 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,26] 2 profile89_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25,26] 2 profile89_node7_cert).mp (by decide +kernel))

def profile89_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node2 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25] 2 (by decide) (choices 3) [19,25,26] profile89_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14,25] (choices 3) [19,25,26] profile89_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node3
  · exact profile89_node6
  · exact profile89_node7

def profile89_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node1 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14] 2 (by decide) (choices 3) [25] profile89_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [14] (choices 3) [25] profile89_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node2

def profile89_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 27 15 23 25 26), lower := (rows 27 15 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 26 30 22 24 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 25 13 29 25 16) }] }

theorem profile89_node11 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,17] 2 profile89_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,17] 2 profile89_node11_cert).mp (by decide +kernel))

def profile89_node12_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 27 15 23 26 25), lower := (rows 27 15 23 26 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 26 14 30 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 25 29 21 24 16) }] }

theorem profile89_node12 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,18] 2 profile89_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19,18] 2 profile89_node12_cert).mp (by decide +kernel))

def profile89_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node10 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19] 2 (by decide) (choices 2) [17,18] profile89_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,19] (choices 2) [17,18] profile89_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node11
  · exact profile89_node12

def profile89_node13_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 27 15 29 27 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 21 0 16) }] }

theorem profile89_node13 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,25] 2 profile89_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,25] 2 profile89_node13_cert).mp (by decide +kernel))

def profile89_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 27 15 30 27 19), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 22 0 16) }] }

theorem profile89_node14 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,26] 2 profile89_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13,26] 2 profile89_node14_cert).mp (by decide +kernel))

def profile89_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node9 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13] 2 (by decide) (choices 3) [19,25,26] profile89_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,13] (choices 3) [19,25,26] profile89_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node10
  · exact profile89_node13
  · exact profile89_node14

def profile89_node16_cert : CutBound 5 := { lost := (rows 0 0 16 0 8), upper := (rows 27 27 15 31 23), lower := (rows 27 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 19 23 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile89_node16 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,11] 2 profile89_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,11] 2 profile89_node16_cert).mp (by decide +kernel))

def profile89_node18_cert : CutBound 5 := { lost := (rows 0 0 2 16 0), upper := (rows 27 27 29 11 22), lower := (rows 27 27 29 11 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 13 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 11 11 13 11 0) }] }

theorem profile89_node18 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,3] 2 profile89_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,3] 2 profile89_node18_cert).mp (by decide +kernel))

def profile89_node19_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 27 27 29 14 19), lower := (rows 27 27 29 14 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 12 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 19 21 22 16) }] }

theorem profile89_node19 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,6] 2 profile89_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25,6] 2 profile89_node19_cert).mp (by decide +kernel))

def profile89_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node17 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25] 2 (by decide) (choices 2) [3,6] profile89_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,25] (choices 2) [3,6] profile89_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node18
  · exact profile89_node19

def profile89_node21_cert : CutBound 5 := { lost := (rows 0 0 1 16 0), upper := (rows 27 27 30 11 21), lower := (rows 27 27 30 11 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 14 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 11 11 14 11 0) }] }

theorem profile89_node21 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,3] 2 profile89_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,3] 2 profile89_node21_cert).mp (by decide +kernel))

def profile89_node22_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 27 27 30 13 19), lower := (rows 27 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 12 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 19 22 21 16) }] }

theorem profile89_node22 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,5] 2 profile89_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26,5] 2 profile89_node22_cert).mp (by decide +kernel))

def profile89_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node20 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26] 2 (by decide) (choices 2) [3,5] profile89_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25,26] (choices 2) [3,5] profile89_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node21
  · exact profile89_node22

def profile89_node15_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node15 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25] 2 (by decide) (choices 3) [11,25,26] profile89_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,25] (choices 3) [11,25,26] profile89_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node16
  · exact profile89_node17
  · exact profile89_node20

def profile89_node24_cert : CutBound 5 := { lost := (rows 0 0 16 0 8), upper := (rows 27 30 15 27 19), lower := (rows 27 30 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 21), good := (rows 19 22 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile89_node24 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,11] 2 profile89_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,11] 2 profile89_node24_cert).mp (by decide +kernel))

def profile89_node25_cert : CutBound 5 := { lost := (rows 0 1 2 0 0), upper := (rows 27 30 29 11 19), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) }] }

theorem profile89_node25 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,25] 2 profile89_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28,25] 2 profile89_node25_cert).mp (by decide +kernel))

def profile89_node23_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node23 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28] 2 (by decide) (choices 3) [11,25] profile89_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26,28] (choices 3) [11,25] profile89_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node24
  · exact profile89_node25

def profile89_node8_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node8 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26] 2 (by decide) (choices 3) [13,25,28] profile89_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [26] (choices 3) [13,25,28] profile89_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node9
  · exact profile89_node15
  · exact profile89_node23

def profile89_node28_cert : CutBound 5 := { lost := (rows 0 0 16 0 8), upper := (rows 29 27 15 27 19), lower := (rows 29 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 13 15 15 8 0) }] }

theorem profile89_node28 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,11] 2 profile89_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,11] 2 profile89_node28_cert).mp (by decide +kernel))

def profile89_node29_cert : CutBound 5 := { lost := (rows 2 0 1 0 0), upper := (rows 29 27 30 11 19), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) },{ target := 1, region := (rows 5 0 4 8 16), good := (rows 29 25 29 8 16) }] }

theorem profile89_node29 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,26] 2 profile89_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25,26] 2 profile89_node29_cert).mp (by decide +kernel))

def profile89_node27_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node27 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25] 2 (by decide) (choices 3) [11,26] profile89_node27_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28,25] (choices 3) [11,26] profile89_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node28
  · exact profile89_node29

def profile89_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node26 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28] 2 (by decide) (choices 3) [25] profile89_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [28] (choices 3) [25] profile89_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node27

def profile89_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node0 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [] 2 (by decide) (choices 3) [14,26,28] profile89_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [] (choices 3) [14,26,28] profile89_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node1
  · exact profile89_node8
  · exact profile89_node26

theorem profile89 : Upper (D (n:=5) [51,51,49,35,35]) (R (n:=5) [51,51,49,35,35]) [] 2 := profile89_node0

def profile90_node4_cert : CutBound 5 := { lost := (rows 0 0 2 6 5), upper := (rows 15 23 29 25 26), lower := (rows 15 23 29 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 28 24 16) },{ target := 1, region := (rows 1 0 14 14 16), good := (rows 13 29 29 29 16) },{ target := 2, region := (rows 1 2 0 15 19), good := (rows 27 27 25 25 16) }] }

theorem profile90_node4 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,17] 2 profile90_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,17] 2 profile90_node4_cert).mp (by decide +kernel))

def profile90_node5_cert : CutBound 5 := { lost := (rows 0 0 2 5 6), upper := (rows 15 23 29 26 25), lower := (rows 15 23 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 28 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 11 23), good := (rows 27 27 25 26 16) }] }

theorem profile90_node5 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,18] 2 profile90_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25,18] 2 profile90_node5_cert).mp (by decide +kernel))

def profile90_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node3 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25] 2 (by decide) (choices 2) [17,18] profile90_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,25] (choices 2) [17,18] profile90_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node4
  · exact profile90_node5

def profile90_node6_cert : CutBound 5 := { lost := (rows 16 0 0 6 6), upper := (rows 15 23 30 25 25), lower := (rows 15 23 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile90_node6 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,26] 2 profile90_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21,26] 2 profile90_node6_cert).mp (by decide +kernel))

def profile90_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node2 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21] 2 (by decide) (choices 3) [25,26] profile90_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,21] (choices 3) [25,26] profile90_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node3
  · exact profile90_node6

def profile90_node9_cert : CutBound 5 := { lost := (rows 0 4 0 6 3), upper := (rows 15 27 23 25 28), lower := (rows 15 27 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 26 22 24 16) },{ target := 1, region := (rows 1 0 4 15 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 14 0 14 16), good := (rows 11 27 27 27 16) }] }

theorem profile90_node9 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,17] 2 profile90_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,17] 2 profile90_node9_cert).mp (by decide +kernel))

def profile90_node10_cert : CutBound 5 := { lost := (rows 0 4 0 3 6), upper := (rows 15 27 23 28 25), lower := (rows 15 27 23 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 23), good := (rows 29 25 29 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 27 19 24 16) }] }

theorem profile90_node10 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,20] 2 profile90_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19,20] 2 profile90_node10_cert).mp (by decide +kernel))

def profile90_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node8 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19] 2 (by decide) (choices 2) [17,20] profile90_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,19] (choices 2) [17,20] profile90_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node9
  · exact profile90_node10

def profile90_node12_cert : CutBound 5 := { lost := (rows 0 4 2 6 1), upper := (rows 15 27 29 25 22), lower := (rows 15 27 29 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 26 28 24 16) },{ target := 1, region := (rows 1 0 14 14 16), good := (rows 13 29 29 29 16) },{ target := 2, region := (rows 1 14 0 14 16), good := (rows 11 27 27 27 16) }] }

theorem profile90_node12 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,17] 2 profile90_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,17] 2 profile90_node12_cert).mp (by decide +kernel))

def profile90_node13_cert : CutBound 5 := { lost := (rows 0 4 2 5 2), upper := (rows 15 27 29 26 21), lower := (rows 15 27 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 6 0 14 16), good := (rows 11 27 27 26 16) }] }

theorem profile90_node13 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,18] 2 profile90_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,18] 2 profile90_node13_cert).mp (by decide +kernel))

def profile90_node14_cert : CutBound 5 := { lost := (rows 0 4 2 3 4), upper := (rows 15 27 29 28 19), lower := (rows 15 27 29 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 26 28 28 16) },{ target := 1, region := (rows 1 0 6 14 16), good := (rows 13 29 29 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) }] }

theorem profile90_node14 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,20] 2 profile90_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25,20] 2 profile90_node14_cert).mp (by decide +kernel))

def profile90_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node11 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25] 2 (by decide) (choices 2) [17,18,20] profile90_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,25] (choices 2) [17,18,20] profile90_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node12
  · exact profile90_node13
  · exact profile90_node14

def profile90_node15_cert : CutBound 5 := { lost := (rows 16 0 1 2 10), upper := (rows 15 27 30 29 21), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 15 11 15 8 0) }] }

theorem profile90_node15 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,26] 2 profile90_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25,26] 2 profile90_node15_cert).mp (by decide +kernel))

def profile90_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node7 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25] 2 (by decide) (choices 3) [19,25,26] profile90_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,25] (choices 3) [19,25,26] profile90_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node8
  · exact profile90_node11
  · exact profile90_node15

def profile90_node17_cert : CutBound 5 := { lost := (rows 16 0 0 6 6), upper := (rows 15 30 23 25 25), lower := (rows 15 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile90_node17 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,19] 2 profile90_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,19] 2 profile90_node17_cert).mp (by decide +kernel))

def profile90_node18_cert : CutBound 5 := { lost := (rows 16 1 0 4 12), upper := (rows 15 30 29 27 19), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 13 8 0) }] }

theorem profile90_node18 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,25] 2 profile90_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28,25] 2 profile90_node18_cert).mp (by decide +kernel))

def profile90_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node16 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28] 2 (by decide) (choices 3) [19,25] profile90_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14,28] (choices 3) [19,25] profile90_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node17
  · exact profile90_node18

def profile90_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node1 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14] 2 (by decide) (choices 3) [21,25,28] profile90_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [14] (choices 3) [21,25,28] profile90_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node2
  · exact profile90_node7
  · exact profile90_node16

def profile90_node22_cert : CutBound 5 := { lost := (rows 4 0 0 6 3), upper := (rows 27 15 23 25 28), lower := (rows 27 15 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 30 22 24 16) },{ target := 1, region := (rows 1 0 4 15 22), good := (rows 25 29 29 25 16) },{ target := 2, region := (rows 5 2 0 13 16), good := (rows 27 11 27 25 16) }] }

theorem profile90_node22 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,17] 2 profile90_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,17] 2 profile90_node22_cert).mp (by decide +kernel))

def profile90_node23_cert : CutBound 5 := { lost := (rows 4 0 0 3 6), upper := (rows 27 15 23 28 25), lower := (rows 27 15 23 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 26 14 30 28 16) },{ target := 1, region := (rows 1 0 4 14 23), good := (rows 25 29 29 28 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 19 24 16) }] }

theorem profile90_node23 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,20] 2 profile90_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19,20] 2 profile90_node23_cert).mp (by decide +kernel))

def profile90_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node21 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19] 2 (by decide) (choices 2) [17,20] profile90_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,19] (choices 2) [17,20] profile90_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node22
  · exact profile90_node23

def profile90_node25_cert : CutBound 5 := { lost := (rows 0 0 2 6 9), upper := (rows 27 15 29 25 22), lower := (rows 27 15 29 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 30 28 24 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 29 13 29 29 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 11 25 25 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 21 17 16) }] }

theorem profile90_node25 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,17] 2 profile90_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,17] 2 profile90_node25_cert).mp (by decide +kernel))

def profile90_node26_cert : CutBound 5 := { lost := (rows 4 0 2 5 2), upper := (rows 27 15 29 26 21), lower := (rows 27 15 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 26 14 28 26 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 9 2 0 9 16), good := (rows 27 11 25 27 16) }] }

theorem profile90_node26 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,18] 2 profile90_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,18] 2 profile90_node26_cert).mp (by decide +kernel))

def profile90_node27_cert : CutBound 5 := { lost := (rows 4 0 2 3 4), upper := (rows 27 15 29 28 19), lower := (rows 27 15 29 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 26 14 28 28 16) },{ target := 1, region := (rows 1 0 5 13 16), good := (rows 29 13 29 28 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 24 16) }] }

theorem profile90_node27 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,20] 2 profile90_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25,20] 2 profile90_node27_cert).mp (by decide +kernel))

def profile90_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node24 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25] 2 (by decide) (choices 2) [17,18,20] profile90_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,25] (choices 2) [17,18,20] profile90_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node25
  · exact profile90_node26
  · exact profile90_node27

def profile90_node28_cert : CutBound 5 := { lost := (rows 4 0 1 2 10), upper := (rows 27 15 30 29 21), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 11 27 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 22 0 16) }] }

theorem profile90_node28 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,26] 2 profile90_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13,26] 2 profile90_node28_cert).mp (by decide +kernel))

def profile90_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node20 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13] 2 (by decide) (choices 3) [19,25,26] profile90_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,13] (choices 3) [19,25,26] profile90_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node21
  · exact profile90_node24
  · exact profile90_node28

def profile90_node30_cert : CutBound 5 := { lost := (rows 4 4 0 2 10), upper := (rows 27 27 15 29 21), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 19 23 0 16) }] }

theorem profile90_node30 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,11] 2 profile90_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,11] 2 profile90_node30_cert).mp (by decide +kernel))

def profile90_node32_cert : CutBound 5 := { lost := (rows 4 4 2 18 0), upper := (rows 27 27 29 13 22), lower := (rows 27 27 29 13 16), losses := [{ target := 1, region := (rows 1 0 7 15 16), good := (rows 29 29 29 13 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 11 16) },{ target := 4, region := (rows 1 2 4 12 0), good := (rows 11 11 13 13 0) }] }

theorem profile90_node32 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,5] 2 profile90_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,5] 2 profile90_node32_cert).mp (by decide +kernel))

def profile90_node33_cert : CutBound 5 := { lost := (rows 4 4 2 0 10), upper := (rows 27 27 29 14 21), lower := (rows 27 27 29 14 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 11 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 19 21 22 16) }] }

theorem profile90_node33 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,6] 2 profile90_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25,6] 2 profile90_node33_cert).mp (by decide +kernel))

def profile90_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node31 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25] 2 (by decide) (choices 2) [5,6] profile90_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,25] (choices 2) [5,6] profile90_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node32
  · exact profile90_node33

def profile90_node35_cert : CutBound 5 := { lost := (rows 4 4 1 0 10), upper := (rows 27 27 30 13 21), lower := (rows 27 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 12 16) },{ target := 1, region := (rows 1 0 4 8 24), good := (rows 25 25 28 29 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 11 16) },{ target := 3, region := (rows 1 2 4 0 24), good := (rows 19 19 22 21 16) }] }

theorem profile90_node35 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26,5] 2 profile90_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26,5] 2 profile90_node35_cert).mp (by decide +kernel))

def profile90_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node34 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26] 2 (by decide) (choices 2) [5] profile90_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25,26] (choices 2) [5] profile90_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile90_node35

def profile90_node29_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile90_node29 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25] 2 (by decide) (choices 3) [11,25,26] profile90_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,25] (choices 3) [11,25,26] profile90_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node30
  · exact profile90_node31
  · exact profile90_node34

def profile90_node37_cert : CutBound 5 := { lost := (rows 4 0 16 2 10), upper := (rows 27 30 15 29 21), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 22 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile90_node37 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,11] 2 profile90_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,11] 2 profile90_node37_cert).mp (by decide +kernel))

def profile90_node39_cert : CutBound 5 := { lost := (rows 4 1 2 4 2), upper := (rows 27 30 29 11 21), lower := (rows 27 30 29 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 10 16) },{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 28 29 29 16) },{ target := 2, region := (rows 3 2 0 11 16), good := (rows 27 27 25 11 16) }] }

theorem profile90_node39 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,3] 2 profile90_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,3] 2 profile90_node39_cert).mp (by decide +kernel))

def profile90_node40_cert : CutBound 5 := { lost := (rows 4 1 2 2 4), upper := (rows 27 30 29 13 19), lower := (rows 27 30 29 13 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 14 16) },{ target := 1, region := (rows 1 0 5 13 16), good := (rows 29 28 29 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 25 16) }] }

theorem profile90_node40 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,5] 2 profile90_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25,5] 2 profile90_node40_cert).mp (by decide +kernel))

def profile90_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node38 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25] 2 (by decide) (choices 2) [3,5] profile90_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28,25] (choices 2) [3,5] profile90_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node39
  · exact profile90_node40

def profile90_node36_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile90_node36 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28] 2 (by decide) (choices 3) [11,25] profile90_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26,28] (choices 3) [11,25] profile90_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node37
  · exact profile90_node38

def profile90_node19_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile90_node19 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26] 2 (by decide) (choices 3) [13,25,28] profile90_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [26] (choices 3) [13,25,28] profile90_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node20
  · exact profile90_node29
  · exact profile90_node36

def profile90_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile90_node0 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [] 2 (by decide) (choices 3) [14,26] profile90_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [] (choices 3) [14,26] profile90_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node1
  · exact profile90_node19

theorem profile90 : Upper (D (n:=5) [51,50,50,35,35]) (R (n:=5) [51,50,50,35,35]) [] 2 := profile90_node0

#print axioms profile90
end Delivery.FiveVertexPositive13
