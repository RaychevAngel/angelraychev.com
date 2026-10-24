import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile51_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 15 31 27 27), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile51_node2 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,13] 2 profile51_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,13] 2 profile51_node2_cert).mp (by decide +kernel))

def profile51_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 23 15 11 27), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile51_node3 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,21] 2 profile51_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,21] 2 profile51_node3_cert).mp (by decide +kernel))

def profile51_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 2), upper := (rows 15 27 15 11 21), lower := (rows 15 27 15 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 11 27 11 11 16) }] }

theorem profile51_node6 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,3] 2 profile51_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,3] 2 profile51_node6_cert).mp (by decide +kernel))

def profile51_node7_cert : CutBound 5 := { lost := (rows 0 4 0 2 4), upper := (rows 15 27 15 13 19), lower := (rows 15 27 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 13 13 16) },{ target := 2, region := (rows 1 15 0 8 31), good := (rows 27 27 27 27 16) }] }

theorem profile51_node7 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,5] 2 profile51_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11,5] 2 profile51_node7_cert).mp (by decide +kernel))

def profile51_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node5 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11] 2 (by decide) (choices 2) [3,5] profile51_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25,11] (choices 2) [3,5] profile51_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node6
  · exact profile51_node7

def profile51_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node4 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25] 2 (by decide) (choices 3) [11] profile51_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14,25] (choices 3) [11] profile51_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node5

def profile51_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node1 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14] 2 (by decide) (choices 3) [13,21,25] profile51_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [14] (choices 3) [13,21,25] profile51_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node2
  · exact profile51_node3
  · exact profile51_node4

def profile51_node9_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 23 15 15 11 27), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile51_node9 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22,13] 2 profile51_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22,13] 2 profile51_node9_cert).mp (by decide +kernel))

def profile51_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node8 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22] 2 (by decide) (choices 3) [13] profile51_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [22] (choices 3) [13] profile51_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node9

def profile51_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 2), upper := (rows 27 15 15 11 21), lower := (rows 27 15 15 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 29 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 11 11 11 16) }] }

theorem profile51_node13 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,3] 2 profile51_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,3] 2 profile51_node13_cert).mp (by decide +kernel))

def profile51_node14_cert : CutBound 5 := { lost := (rows 4 0 0 2 4), upper := (rows 27 15 15 13 19), lower := (rows 27 15 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 13 13 16) },{ target := 2, region := (rows 7 2 0 8 23), good := (rows 27 27 27 25 16) }] }

theorem profile51_node14 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,5] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,5] 2 profile51_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11,5] 2 profile51_node14_cert).mp (by decide +kernel))

def profile51_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node12 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11] 2 (by decide) (choices 2) [3,5] profile51_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13,11] (choices 2) [3,5] profile51_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node13
  · exact profile51_node14

def profile51_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node11 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13] 2 (by decide) (choices 3) [11] profile51_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26,13] (choices 3) [11] profile51_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node12

def profile51_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node10 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26] 2 (by decide) (choices 3) [13] profile51_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [26] (choices 3) [13] profile51_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node11

def profile51_node16_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 29 15 15 11 27), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile51_node16 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28,13] 2 profile51_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28,13] 2 profile51_node16_cert).mp (by decide +kernel))

def profile51_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node15 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28] 2 (by decide) (choices 3) [13] profile51_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [28] (choices 3) [13] profile51_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node16

def profile51_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node0 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [] 2 (by decide) (choices 3) [14,22,26,28] profile51_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [] (choices 3) [14,22,26,28] profile51_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile51_node1
  · exact profile51_node8
  · exact profile51_node10
  · exact profile51_node15

theorem profile51 : Upper (D (n:=5) [52,51,50,35,33]) (R (n:=5) [52,51,50,35,33]) [] 2 := profile51_node0

def profile52_node4_cert : CutBound 5 := { lost := (rows 0 0 0 0 9), upper := (rows 15 15 15 25 22), lower := (rows 15 15 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 30 24 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 17 16) }] }

theorem profile52_node4 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,17] 2 profile52_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,17] 2 profile52_node4_cert).mp (by decide +kernel))

def profile52_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 10), upper := (rows 15 15 15 26 21), lower := (rows 15 15 15 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 29 24 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 18 16) }] }

theorem profile52_node5 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,18] 2 profile52_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,18] 2 profile52_node5_cert).mp (by decide +kernel))

def profile52_node6_cert : CutBound 5 := { lost := (rows 0 0 0 0 12), upper := (rows 15 15 15 28 19), lower := (rows 15 15 15 28 16), losses := [{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 27 24 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 20 16) }] }

theorem profile52_node6 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,20] 2 profile52_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11,20] 2 profile52_node6_cert).mp (by decide +kernel))

def profile52_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node3 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11] 2 (by decide) (choices 2) [17,18,20] profile52_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,11] (choices 2) [17,18,20] profile52_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node4
  · exact profile52_node5
  · exact profile52_node6

def profile52_node8_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 15 15 23 11 28), lower := (rows 15 15 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 25 16) }] }

theorem profile52_node8 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,3] 2 profile52_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,3] 2 profile52_node8_cert).mp (by decide +kernel))

def profile52_node9_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 15 15 23 13 26), lower := (rows 15 15 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 13 29 13 16) }] }

theorem profile52_node9 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,5] 2 profile52_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,5] 2 profile52_node9_cert).mp (by decide +kernel))

def profile52_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 15 15 23 14 25), lower := (rows 15 15 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 28 16) }] }

theorem profile52_node10 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,6] 2 profile52_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19,6] 2 profile52_node10_cert).mp (by decide +kernel))

def profile52_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node7 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19] 2 (by decide) (choices 2) [3,5,6] profile52_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,19] (choices 2) [3,5,6] profile52_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node8
  · exact profile52_node9
  · exact profile52_node10

def profile52_node12_cert : CutBound 5 := { lost := (rows 0 0 0 4 1), upper := (rows 15 15 29 11 22), lower := (rows 15 15 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 26 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 25 11 16) }] }

theorem profile52_node12 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,3] 2 profile52_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,3] 2 profile52_node12_cert).mp (by decide +kernel))

def profile52_node13_cert : CutBound 5 := { lost := (rows 0 0 0 1 4), upper := (rows 15 15 29 14 19), lower := (rows 15 15 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 25 26 16) }] }

theorem profile52_node13 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,6] 2 profile52_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25,6] 2 profile52_node13_cert).mp (by decide +kernel))

def profile52_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node11 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25] 2 (by decide) (choices 2) [3,6] profile52_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,25] (choices 2) [3,6] profile52_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node12
  · exact profile52_node13

def profile52_node15_cert : CutBound 5 := { lost := (rows 0 0 0 4 2), upper := (rows 15 15 30 11 21), lower := (rows 15 15 30 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 28 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 26 11 16) }] }

theorem profile52_node15 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,3] 2 profile52_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,3] 2 profile52_node15_cert).mp (by decide +kernel))

def profile52_node16_cert : CutBound 5 := { lost := (rows 0 0 0 2 4), upper := (rows 15 15 30 13 19), lower := (rows 15 15 30 13 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 26 25 16) }] }

theorem profile52_node16 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,5] 2 profile52_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26,5] 2 profile52_node16_cert).mp (by decide +kernel))

def profile52_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node14 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26] 2 (by decide) (choices 2) [3,5] profile52_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13,26] (choices 2) [3,5] profile52_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node15
  · exact profile52_node16

def profile52_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node2 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13] 2 (by decide) (choices 3) [11,19,25,26] profile52_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,13] (choices 3) [11,19,25,26] profile52_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile52_node3
  · exact profile52_node7
  · exact profile52_node11
  · exact profile52_node14

def profile52_node19_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 15 23 15 11 28), lower := (rows 15 23 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 25 16) }] }

theorem profile52_node19 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,3] 2 profile52_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,3] 2 profile52_node19_cert).mp (by decide +kernel))

def profile52_node20_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 15 23 15 13 26), lower := (rows 15 23 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 29 13 13 16) }] }

theorem profile52_node20 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,5] 2 profile52_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,5] 2 profile52_node20_cert).mp (by decide +kernel))

def profile52_node21_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 15 23 15 14 25), lower := (rows 15 23 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 28 16) }] }

theorem profile52_node21 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,6] 2 profile52_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11,6] 2 profile52_node21_cert).mp (by decide +kernel))

def profile52_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node18 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11] 2 (by decide) (choices 2) [3,5,6] profile52_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21,11] (choices 2) [3,5,6] profile52_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node19
  · exact profile52_node20
  · exact profile52_node21

def profile52_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node17 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21] 2 (by decide) (choices 3) [11] profile52_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,21] (choices 3) [11] profile52_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node18

def profile52_node24_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 15 27 15 13 22), lower := (rows 15 27 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 13 13 16) }] }

theorem profile52_node24 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,5] 2 profile52_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,5] 2 profile52_node24_cert).mp (by decide +kernel))

def profile52_node25_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 15 27 15 14 21), lower := (rows 15 27 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 28 16) }] }

theorem profile52_node25 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,6] 2 profile52_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11,6] 2 profile52_node25_cert).mp (by decide +kernel))

def profile52_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node23 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11] 2 (by decide) (choices 2) [5,6] profile52_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25,11] (choices 2) [5,6] profile52_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node24
  · exact profile52_node25

def profile52_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node22 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25] 2 (by decide) (choices 3) [11] profile52_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,25] (choices 3) [11] profile52_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node23

def profile52_node28_cert : CutBound 5 := { lost := (rows 0 0 0 4 2), upper := (rows 15 30 15 11 21), lower := (rows 15 30 15 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 29 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 11 26 11 11 16) }] }

theorem profile52_node28 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,3] 2 profile52_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,3] 2 profile52_node28_cert).mp (by decide +kernel))

def profile52_node29_cert : CutBound 5 := { lost := (rows 0 0 0 2 4), upper := (rows 15 30 15 13 19), lower := (rows 15 30 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 27 25 16) }] }

theorem profile52_node29 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,5] 2 profile52_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11,5] 2 profile52_node29_cert).mp (by decide +kernel))

def profile52_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node27 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11] 2 (by decide) (choices 2) [3,5] profile52_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28,11] (choices 2) [3,5] profile52_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node28
  · exact profile52_node29

def profile52_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node26 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28] 2 (by decide) (choices 3) [11] profile52_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14,28] (choices 3) [11] profile52_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node27

def profile52_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node1 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile52_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [14] (choices 3) [13,21,25,28] profile52_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile52_node2
  · exact profile52_node17
  · exact profile52_node22
  · exact profile52_node26

def profile52_node33_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 23 15 15 11 28), lower := (rows 23 15 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 30 26 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 29 29 25 16) }] }

theorem profile52_node33 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,3] 2 profile52_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,3] 2 profile52_node33_cert).mp (by decide +kernel))

def profile52_node34_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 23 15 15 13 26), lower := (rows 23 15 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 30 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) }] }

theorem profile52_node34 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,5] 2 profile52_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,5] 2 profile52_node34_cert).mp (by decide +kernel))

def profile52_node35_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 23 15 15 14 25), lower := (rows 23 15 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 29 29 28 16) }] }

theorem profile52_node35 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,6] 2 profile52_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11,6] 2 profile52_node35_cert).mp (by decide +kernel))

def profile52_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node32 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11] 2 (by decide) (choices 2) [3,5,6] profile52_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13,11] (choices 2) [3,5,6] profile52_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node33
  · exact profile52_node34
  · exact profile52_node35

def profile52_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node31 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13] 2 (by decide) (choices 3) [11] profile52_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22,13] (choices 3) [11] profile52_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node32

def profile52_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node30 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22] 2 (by decide) (choices 3) [13] profile52_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [22] (choices 3) [13] profile52_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node31

def profile52_node39_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 27 15 15 13 22), lower := (rows 27 15 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 30 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 13 13 16) }] }

theorem profile52_node39 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,5] 2 profile52_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,5] 2 profile52_node39_cert).mp (by decide +kernel))

def profile52_node40_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 27 15 15 14 21), lower := (rows 27 15 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 29 28 16) }] }

theorem profile52_node40 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,6] 2 profile52_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11,6] 2 profile52_node40_cert).mp (by decide +kernel))

def profile52_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node38 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11] 2 (by decide) (choices 2) [5,6] profile52_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13,11] (choices 2) [5,6] profile52_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile52_node39
  · exact profile52_node40

def profile52_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node37 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13] 2 (by decide) (choices 3) [11] profile52_node37_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26,13] (choices 3) [11] profile52_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node38

def profile52_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node36 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26] 2 (by decide) (choices 3) [13] profile52_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [26] (choices 3) [13] profile52_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node37

def profile52_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile52_node0 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [] 2 (by decide) (choices 3) [14,22,26] profile52_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [] (choices 3) [14,22,26] profile52_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node1
  · exact profile52_node30
  · exact profile52_node36

theorem profile52 : Upper (D (n:=5) [51,51,51,35,33]) (R (n:=5) [51,51,51,35,33]) [] 2 := profile52_node0

def profile53_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 13 14 30), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile53_node3 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,9] 2 profile53_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,9] 2 profile53_node3_cert).mp (by decide +kernel))

def profile53_node4_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 31 15 14 13 29), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile53_node4 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,10] 2 profile53_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13,10] 2 profile53_node4_cert).mp (by decide +kernel))

def profile53_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node2 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13] 2 (by decide) (choices 2) [9,10] profile53_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30,13] (choices 2) [9,10] profile53_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile53_node3
  · exact profile53_node4

def profile53_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node1 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30] 2 (by decide) (choices 3) [13] profile53_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [30] (choices 3) [13] profile53_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node2

def profile53_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node0 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [] 2 (by decide) (choices 4) [30] profile53_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [] (choices 4) [30] profile53_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node1

theorem profile53 : Upper (D (n:=5) [66,50,36,36,33]) (R (n:=5) [66,50,36,36,33]) [] 2 := profile53_node0

def profile54_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 15 31 27 27), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile54_node2 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,13] 2 profile54_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,13] 2 profile54_node2_cert).mp (by decide +kernel))

def profile54_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 15 27 15 13 29), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile54_node4 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25,11] 2 profile54_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25,11] 2 profile54_node4_cert).mp (by decide +kernel))

def profile54_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node3 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25] 2 (by decide) (choices 3) [11] profile54_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14,25] (choices 3) [11] profile54_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node4

def profile54_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node1 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14] 2 (by decide) (choices 3) [13,25] profile54_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [14] (choices 3) [13,25] profile54_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile54_node2
  · exact profile54_node3

def profile54_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 15 15 13 29), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile54_node7 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13,11] 2 profile54_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13,11] 2 profile54_node7_cert).mp (by decide +kernel))

def profile54_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node6 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13] 2 (by decide) (choices 3) [11] profile54_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26,13] (choices 3) [11] profile54_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node7

def profile54_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node5 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26] 2 (by decide) (choices 3) [13] profile54_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [26] (choices 3) [13] profile54_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node6

def profile54_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile54_node0 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [] 2 (by decide) (choices 3) [14,26] profile54_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [] (choices 3) [14,26] profile54_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile54_node1
  · exact profile54_node5

theorem profile54 : Upper (D (n:=5) [52,50,50,36,33]) (R (n:=5) [52,50,50,36,33]) [] 2 := profile54_node0

def profile55_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 15 31 27 27), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile55_node2 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,13] 2 profile55_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,13] 2 profile55_node2_cert).mp (by decide +kernel))

def profile55_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 15 27 15 11 28), lower := (rows 15 27 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 25 16) }] }

theorem profile55_node5 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,3] 2 profile55_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,3] 2 profile55_node5_cert).mp (by decide +kernel))

def profile55_node6_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 15 27 15 13 26), lower := (rows 15 27 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 13 13 16) }] }

theorem profile55_node6 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,5] 2 profile55_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,5] 2 profile55_node6_cert).mp (by decide +kernel))

def profile55_node7_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 15 27 15 14 25), lower := (rows 15 27 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 25 29 28 16) }] }

theorem profile55_node7 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,6] 2 profile55_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11,6] 2 profile55_node7_cert).mp (by decide +kernel))

def profile55_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node4 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11] 2 (by decide) (choices 2) [3,5,6] profile55_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25,11] (choices 2) [3,5,6] profile55_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node5
  · exact profile55_node6
  · exact profile55_node7

def profile55_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node3 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25] 2 (by decide) (choices 3) [11] profile55_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,25] (choices 3) [11] profile55_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node4

def profile55_node8_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 30 15 11 27), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile55_node8 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,28] 2 profile55_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14,28] 2 profile55_node8_cert).mp (by decide +kernel))

def profile55_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node1 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14] 2 (by decide) (choices 3) [13,25,28] profile55_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [14] (choices 3) [13,25,28] profile55_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node2
  · exact profile55_node3
  · exact profile55_node8

def profile55_node12_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 27 15 15 11 28), lower := (rows 27 15 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 30 26 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 29 25 16) }] }

theorem profile55_node12 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,3] 2 profile55_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,3] 2 profile55_node12_cert).mp (by decide +kernel))

def profile55_node13_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 27 15 15 13 26), lower := (rows 27 15 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 26 30 30 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 13 13 16) }] }

theorem profile55_node13 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,5] 2 profile55_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,5] 2 profile55_node13_cert).mp (by decide +kernel))

def profile55_node14_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 27 15 15 14 25), lower := (rows 27 15 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 25 29 29 28 16) }] }

theorem profile55_node14 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,6] 2 profile55_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11,6] 2 profile55_node14_cert).mp (by decide +kernel))

def profile55_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node11 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11] 2 (by decide) (choices 2) [3,5,6] profile55_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13,11] (choices 2) [3,5,6] profile55_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node12
  · exact profile55_node13
  · exact profile55_node14

def profile55_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node10 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13] 2 (by decide) (choices 3) [11] profile55_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26,13] (choices 3) [11] profile55_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node11

def profile55_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node9 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26] 2 (by decide) (choices 3) [13] profile55_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [26] (choices 3) [13] profile55_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node10

def profile55_node16_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 29 15 15 11 27), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile55_node16 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28,13] 2 profile55_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28,13] 2 profile55_node16_cert).mp (by decide +kernel))

def profile55_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node15 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28] 2 (by decide) (choices 3) [13] profile55_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [28] (choices 3) [13] profile55_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node16

def profile55_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node0 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [] 2 (by decide) (choices 3) [14,26,28] profile55_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [] (choices 3) [14,26,28] profile55_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node1
  · exact profile55_node9
  · exact profile55_node15

theorem profile55 : Upper (D (n:=5) [51,51,50,36,33]) (R (n:=5) [51,51,50,36,33]) [] 2 := profile55_node0

def profile56_node2_cert : CutBound 5 := { lost := (rows 0 16 8 4 12), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile56_node2 : Upper (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30,13] 2 profile56_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30,13] 2 profile56_node2_cert).mp (by decide +kernel))

def profile56_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile56_node1 : Upper (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30] 2 (by decide) (choices 3) [13] profile56_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [30] (choices 3) [13] profile56_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node2

def profile56_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node0 : Upper (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [] 2 (by decide) (choices 4) [30] profile56_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [] (choices 4) [30] profile56_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node1

theorem profile56 : Upper (D (n:=5) [68,51,34,34,34]) (R (n:=5) [68,51,34,34,34]) [] 2 := profile56_node0

def profile57_node2_cert : CutBound 5 := { lost := (rows 0 16 8 4 12), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile57_node2 : Upper (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,13] 2 profile57_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,13] 2 profile57_node2_cert).mp (by decide +kernel))

def profile57_node3_cert : CutBound 5 := { lost := (rows 0 1 8 4 12), upper := (rows 31 30 7 11 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile57_node3 : Upper (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,28] 2 profile57_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30,28] 2 profile57_node3_cert).mp (by decide +kernel))

def profile57_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile57_node1 : Upper (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30] 2 (by decide) (choices 3) [13,28] profile57_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [30] (choices 3) [13,28] profile57_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile57_node2
  · exact profile57_node3

def profile57_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node0 : Upper (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [] 2 (by decide) (choices 4) [30] profile57_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [] (choices 4) [30] profile57_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node1

theorem profile57 : Upper (D (n:=5) [67,52,34,34,34]) (R (n:=5) [67,52,34,34,34]) [] 2 := profile57_node0

def profile58_node3_cert : CutBound 5 := { lost := (rows 0 16 24 2 10), upper := (rows 31 15 7 29 21), lower := (rows 31 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile58_node3 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,3] 2 profile58_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,3] 2 profile58_node3_cert).mp (by decide +kernel))

def profile58_node4_cert : CutBound 5 := { lost := (rows 0 16 10 16 8), upper := (rows 31 15 21 15 23), lower := (rows 31 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile58_node4 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,17] 2 profile58_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13,17] 2 profile58_node4_cert).mp (by decide +kernel))

def profile58_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node2 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13] 2 (by decide) (choices 2) [3,17] profile58_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,13] (choices 2) [3,17] profile58_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile58_node3
  · exact profile58_node4

def profile58_node5_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile58_node5 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,25] 2 profile58_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30,25] 2 profile58_node5_cert).mp (by decide +kernel))

def profile58_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile58_node1 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30] 2 (by decide) (choices 3) [13,25] profile58_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [30] (choices 3) [13,25] profile58_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile58_node2
  · exact profile58_node5

def profile58_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node0 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [] 2 (by decide) (choices 4) [30] profile58_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [] (choices 4) [30] profile58_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node1

theorem profile58 : Upper (D (n:=5) [68,50,35,34,34]) (R (n:=5) [68,50,35,34,34]) [] 2 := profile58_node0

def profile59_node4_cert : CutBound 5 := { lost := (rows 0 0 8 6 9), upper := (rows 31 15 7 25 22), lower := (rows 31 15 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 22 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 25 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile59_node4 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,17] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,17] 2 profile59_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,17] 2 profile59_node4_cert).mp (by decide +kernel))

def profile59_node5_cert : CutBound 5 := { lost := (rows 0 0 8 5 10), upper := (rows 31 15 7 26 21), lower := (rows 31 15 7 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 26 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 21 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 26 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile59_node5 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,18] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,18] 2 profile59_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,18] 2 profile59_node5_cert).mp (by decide +kernel))

def profile59_node6_cert : CutBound 5 := { lost := (rows 0 0 8 3 12), upper := (rows 31 15 7 28 19), lower := (rows 31 15 7 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 28 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 19 24 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 20 16) }] }

theorem profile59_node6 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,20] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,20] 2 profile59_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3,20] 2 profile59_node6_cert).mp (by decide +kernel))

def profile59_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node3 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3] 2 (by decide) (choices 2) [17,18,20] profile59_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,3] (choices 2) [17,18,20] profile59_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile59_node4
  · exact profile59_node5
  · exact profile59_node6

def profile59_node7_cert : CutBound 5 := { lost := (rows 0 16 10 16 8), upper := (rows 31 15 21 15 23), lower := (rows 31 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile59_node7 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,17] 2 profile59_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,17] 2 profile59_node7_cert).mp (by decide +kernel))

def profile59_node8_cert : CutBound 5 := { lost := (rows 0 16 9 16 8), upper := (rows 31 15 22 15 23), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile59_node8 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,18] 2 profile59_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13,18] 2 profile59_node8_cert).mp (by decide +kernel))

def profile59_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node2 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13] 2 (by decide) (choices 2) [3,17,18] profile59_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,13] (choices 2) [3,17,18] profile59_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile59_node3
  · exact profile59_node7
  · exact profile59_node8

def profile59_node9_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile59_node9 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,25] 2 profile59_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,25] 2 profile59_node9_cert).mp (by decide +kernel))

def profile59_node10_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile59_node10 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,28] 2 profile59_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30,28] 2 profile59_node10_cert).mp (by decide +kernel))

def profile59_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile59_node1 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile59_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [30] (choices 3) [13,25,28] profile59_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile59_node2
  · exact profile59_node9
  · exact profile59_node10

def profile59_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node0 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [] 2 (by decide) (choices 4) [30] profile59_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [] (choices 4) [30] profile59_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node1

theorem profile59 : Upper (D (n:=5) [67,51,35,34,34]) (R (n:=5) [67,51,35,34,34]) [] 2 := profile59_node0

def profile60_node3_cert : CutBound 5 := { lost := (rows 0 16 24 1 9), upper := (rows 31 15 7 30 22), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile60_node3 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,3] 2 profile60_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,3] 2 profile60_node3_cert).mp (by decide +kernel))

def profile60_node4_cert : CutBound 5 := { lost := (rows 0 16 9 16 8), upper := (rows 31 15 22 15 23), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile60_node4 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,18] 2 profile60_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13,18] 2 profile60_node4_cert).mp (by decide +kernel))

def profile60_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node2 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13] 2 (by decide) (choices 2) [3,18] profile60_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,13] (choices 2) [3,18] profile60_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile60_node3
  · exact profile60_node4

def profile60_node5_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile60_node5 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,25] 2 profile60_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,25] 2 profile60_node5_cert).mp (by decide +kernel))

def profile60_node6_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile60_node6 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,28] 2 profile60_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30,28] 2 profile60_node6_cert).mp (by decide +kernel))

def profile60_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile60_node1 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile60_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [30] (choices 3) [13,25,28] profile60_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile60_node2
  · exact profile60_node5
  · exact profile60_node6

def profile60_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node0 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [] 2 (by decide) (choices 4) [30] profile60_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [] (choices 4) [30] profile60_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node1

theorem profile60 : Upper (D (n:=5) [66,52,35,34,34]) (R (n:=5) [66,52,35,34,34]) [] 2 := profile60_node0

def profile61_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 21 29 21), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile61_node2 : Upper (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30,13] 2 profile61_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30,13] 2 profile61_node2_cert).mp (by decide +kernel))

def profile61_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile61_node1 : Upper (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30] 2 (by decide) (choices 3) [13] profile61_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [30] (choices 3) [13] profile61_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node2

def profile61_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node0 : Upper (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [] 2 (by decide) (choices 4) [30] profile61_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [] (choices 4) [30] profile61_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node1

theorem profile61 : Upper (D (n:=5) [68,49,36,34,34]) (R (n:=5) [68,49,36,34,34]) [] 2 := profile61_node0

def profile62_node3_cert : CutBound 5 := { lost := (rows 0 16 24 2 10), upper := (rows 31 15 7 29 21), lower := (rows 31 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile62_node3 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,3] 2 profile62_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,3] 2 profile62_node3_cert).mp (by decide +kernel))

def profile62_node4_cert : CutBound 5 := { lost := (rows 0 16 10 16 8), upper := (rows 31 15 21 15 23), lower := (rows 31 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile62_node4 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,17] 2 profile62_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,17] 2 profile62_node4_cert).mp (by decide +kernel))

def profile62_node5_cert : CutBound 5 := { lost := (rows 0 0 9 2 10), upper := (rows 31 15 22 13 21), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile62_node5 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,18] 2 profile62_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13,18] 2 profile62_node5_cert).mp (by decide +kernel))

def profile62_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node2 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13] 2 (by decide) (choices 2) [3,17,18] profile62_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,13] (choices 2) [3,17,18] profile62_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile62_node3
  · exact profile62_node4
  · exact profile62_node5

def profile62_node6_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile62_node6 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,28] 2 profile62_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30,28] 2 profile62_node6_cert).mp (by decide +kernel))

def profile62_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile62_node1 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30] 2 (by decide) (choices 3) [13,28] profile62_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [30] (choices 3) [13,28] profile62_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile62_node2
  · exact profile62_node6

def profile62_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node0 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [] 2 (by decide) (choices 4) [30] profile62_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [] (choices 4) [30] profile62_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node1

theorem profile62 : Upper (D (n:=5) [67,50,36,34,34]) (R (n:=5) [67,50,36,34,34]) [] 2 := profile62_node0

def profile63_node3_cert : CutBound 5 := { lost := (rows 0 16 24 1 9), upper := (rows 31 15 7 30 22), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile63_node3 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,3] 2 profile63_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,3] 2 profile63_node3_cert).mp (by decide +kernel))

def profile63_node4_cert : CutBound 5 := { lost := (rows 0 0 10 1 9), upper := (rows 31 15 21 14 22), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile63_node4 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,17] 2 profile63_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,17] 2 profile63_node4_cert).mp (by decide +kernel))

def profile63_node5_cert : CutBound 5 := { lost := (rows 0 16 9 16 8), upper := (rows 31 15 22 15 23), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile63_node5 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,18] 2 profile63_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13,18] 2 profile63_node5_cert).mp (by decide +kernel))

def profile63_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node2 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13] 2 (by decide) (choices 2) [3,17,18] profile63_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,13] (choices 2) [3,17,18] profile63_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile63_node3
  · exact profile63_node4
  · exact profile63_node5

def profile63_node6_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile63_node6 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,28] 2 profile63_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30,28] 2 profile63_node6_cert).mp (by decide +kernel))

def profile63_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile63_node1 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30] 2 (by decide) (choices 3) [13,28] profile63_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [30] (choices 3) [13,28] profile63_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile63_node2
  · exact profile63_node6

def profile63_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node0 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [] 2 (by decide) (choices 4) [30] profile63_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [] (choices 4) [30] profile63_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile63_node1

theorem profile63 : Upper (D (n:=5) [66,51,36,34,34]) (R (n:=5) [66,51,36,34,34]) [] 2 := profile63_node0

def profile64_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 22 30 22), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile64_node2 : Upper (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,13] 2 profile64_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,13] 2 profile64_node2_cert).mp (by decide +kernel))

def profile64_node3_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile64_node3 : Upper (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,28] 2 profile64_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30,28] 2 profile64_node3_cert).mp (by decide +kernel))

def profile64_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile64_node1 : Upper (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30] 2 (by decide) (choices 3) [13,28] profile64_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [30] (choices 3) [13,28] profile64_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile64_node2
  · exact profile64_node3

def profile64_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile64_node0 : Upper (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [] 2 (by decide) (choices 4) [30] profile64_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [] (choices 4) [30] profile64_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile64_node1

theorem profile64 : Upper (D (n:=5) [65,52,36,34,34]) (R (n:=5) [65,52,36,34,34]) [] 2 := profile64_node0

def profile65_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 27 23 27 19), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile65_node2 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14,25] 2 profile65_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14,25] 2 profile65_node2_cert).mp (by decide +kernel))

def profile65_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile65_node1 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14] 2 (by decide) (choices 3) [25] profile65_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [14] (choices 3) [25] profile65_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile65_node2

def profile65_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 27 15 23 27 19), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile65_node4 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,13] 2 profile65_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,13] 2 profile65_node4_cert).mp (by decide +kernel))

def profile65_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 27 27 7 15 23), lower := (rows 27 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile65_node5 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,25] 2 profile65_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26,25] 2 profile65_node5_cert).mp (by decide +kernel))

def profile65_node3_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile65_node3 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26] 2 (by decide) (choices 3) [13,25] profile65_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [26] (choices 3) [13,25] profile65_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile65_node4
  · exact profile65_node5

def profile65_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile65_node0 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [] 2 (by decide) (choices 3) [14,26] profile65_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [] (choices 3) [14,26] profile65_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile65_node1
  · exact profile65_node3

theorem profile65 : Upper (D (n:=5) [52,52,49,34,34]) (R (n:=5) [52,52,49,34,34]) [] 2 := profile65_node0

def profile66_node2_cert : CutBound 5 := { lost := (rows 16 16 8 4 12), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile66_node2 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,13] 2 profile66_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,13] 2 profile66_node2_cert).mp (by decide +kernel))

def profile66_node4_cert : CutBound 5 := { lost := (rows 16 8 16 4 12), upper := (rows 15 23 15 27 19), lower := (rows 15 23 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile66_node4 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,11] 2 profile66_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,11] 2 profile66_node4_cert).mp (by decide +kernel))

def profile66_node5_cert : CutBound 5 := { lost := (rows 16 8 8 20 4), upper := (rows 15 23 23 11 27), lower := (rows 15 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile66_node5 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,19] 2 profile66_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,19] 2 profile66_node5_cert).mp (by decide +kernel))

def profile66_node6_cert : CutBound 5 := { lost := (rows 16 8 0 20 12), upper := (rows 15 23 29 11 19), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile66_node6 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,25] 2 profile66_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21,25] 2 profile66_node6_cert).mp (by decide +kernel))

def profile66_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node3 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21] 2 (by decide) (choices 3) [11,19,25] profile66_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,21] (choices 3) [11,19,25] profile66_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node4
  · exact profile66_node5
  · exact profile66_node6

def profile66_node9_cert : CutBound 5 := { lost := (rows 0 4 8 4 10), upper := (rows 15 27 23 11 21), lower := (rows 15 27 23 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 21 25 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 2 15 0 31), good := (rows 23 23 23 23 16) }] }

theorem profile66_node9 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,3] 2 profile66_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,3] 2 profile66_node9_cert).mp (by decide +kernel))

def profile66_node10_cert : CutBound 5 := { lost := (rows 0 4 8 2 12), upper := (rows 15 27 23 13 19), lower := (rows 15 27 23 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 29 13 16) },{ target := 2, region := (rows 1 11 0 8 31), good := (rows 27 27 19 27 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile66_node10 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,5] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,5] 2 profile66_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19,5] 2 profile66_node10_cert).mp (by decide +kernel))

def profile66_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node8 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19] 2 (by decide) (choices 2) [3,5] profile66_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25,19] (choices 2) [3,5] profile66_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile66_node9
  · exact profile66_node10

def profile66_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node7 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25] 2 (by decide) (choices 3) [19] profile66_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14,25] (choices 3) [19] profile66_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node8

def profile66_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node1 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14] 2 (by decide) (choices 3) [13,21,25] profile66_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [14] (choices 3) [13,21,25] profile66_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node2
  · exact profile66_node3
  · exact profile66_node7

def profile66_node14_cert : CutBound 5 := { lost := (rows 4 0 8 4 10), upper := (rows 27 15 23 11 21), lower := (rows 27 15 23 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 21 25 16) },{ target := 2, region := (rows 5 2 0 15 16), good := (rows 27 11 27 11 16) },{ target := 3, region := (rows 1 2 15 0 31), good := (rows 23 23 23 23 16) }] }

theorem profile66_node14 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,3] 2 profile66_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,3] 2 profile66_node14_cert).mp (by decide +kernel))

def profile66_node15_cert : CutBound 5 := { lost := (rows 4 0 8 2 12), upper := (rows 27 15 23 13 19), lower := (rows 27 15 23 13 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 29 13 16) },{ target := 2, region := (rows 3 2 0 8 23), good := (rows 27 27 19 25 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile66_node15 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,5] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,5] 2 profile66_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19,5] 2 profile66_node15_cert).mp (by decide +kernel))

def profile66_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node13 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19] 2 (by decide) (choices 2) [3,5] profile66_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13,19] (choices 2) [3,5] profile66_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile66_node14
  · exact profile66_node15

def profile66_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node12 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13] 2 (by decide) (choices 3) [19] profile66_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,13] (choices 3) [19] profile66_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node13

def profile66_node16_cert : CutBound 5 := { lost := (rows 4 4 24 16 8), upper := (rows 27 27 7 15 23), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile66_node16 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,25] 2 profile66_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26,25] 2 profile66_node16_cert).mp (by decide +kernel))

def profile66_node11_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile66_node11 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26] 2 (by decide) (choices 3) [13,25] profile66_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [26] (choices 3) [13,25] profile66_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile66_node12
  · exact profile66_node16

def profile66_node18_cert : CutBound 5 := { lost := (rows 0 16 8 4 12), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile66_node18 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,13] 2 profile66_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,13] 2 profile66_node18_cert).mp (by decide +kernel))

def profile66_node19_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 29 27 7 15 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile66_node19 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,25] 2 profile66_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28,25] 2 profile66_node19_cert).mp (by decide +kernel))

def profile66_node17_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile66_node17 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28] 2 (by decide) (choices 3) [13,25] profile66_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [28] (choices 3) [13,25] profile66_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile66_node18
  · exact profile66_node19

def profile66_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile66_node0 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [] 2 (by decide) (choices 3) [14,26,28] profile66_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [] (choices 3) [14,26,28] profile66_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node1
  · exact profile66_node11
  · exact profile66_node17

theorem profile66 : Upper (D (n:=5) [52,51,50,34,34]) (R (n:=5) [52,51,50,34,34]) [] 2 := profile66_node0

#print axioms profile66
end Delivery.FiveVertexPositive13
