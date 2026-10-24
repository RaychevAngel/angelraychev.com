import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile76_node3_cert : CutBound 5 := { lost := (rows 16 16 0 6 6), upper := (rows 15 15 23 25 25), lower := (rows 15 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile76_node3 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,19] 2 profile76_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,19] 2 profile76_node3_cert).mp (by decide +kernel))

def profile76_node4_cert : CutBound 5 := { lost := (rows 16 16 0 4 12), upper := (rows 15 15 29 27 19), lower := (rows 15 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node4 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,25] 2 profile76_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13,25] 2 profile76_node4_cert).mp (by decide +kernel))

def profile76_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node2 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13] 2 (by decide) (choices 3) [19,25] profile76_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,13] (choices 3) [19,25] profile76_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node3
  · exact profile76_node4

def profile76_node6_cert : CutBound 5 := { lost := (rows 16 0 16 6 6), upper := (rows 15 23 15 25 25), lower := (rows 15 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile76_node6 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,11] 2 profile76_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,11] 2 profile76_node6_cert).mp (by decide +kernel))

def profile76_node7_cert : CutBound 5 := { lost := (rows 16 8 0 20 4), upper := (rows 15 23 29 11 27), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile76_node7 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,25] 2 profile76_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21,25] 2 profile76_node7_cert).mp (by decide +kernel))

def profile76_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node5 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21] 2 (by decide) (choices 3) [11,25] profile76_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,21] (choices 3) [11,25] profile76_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node6
  · exact profile76_node7

def profile76_node9_cert : CutBound 5 := { lost := (rows 16 0 16 2 10), upper := (rows 15 27 15 29 21), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node9 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,11] 2 profile76_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,11] 2 profile76_node9_cert).mp (by decide +kernel))

def profile76_node10_cert : CutBound 5 := { lost := (rows 16 0 8 18 2), upper := (rows 15 27 23 13 29), lower := (rows 15 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile76_node10 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,19] 2 profile76_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,19] 2 profile76_node10_cert).mp (by decide +kernel))

def profile76_node12_cert : CutBound 5 := { lost := (rows 0 4 2 4 10), upper := (rows 15 27 29 11 21), lower := (rows 15 27 29 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 21 19 16) }] }

theorem profile76_node12 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,3] 2 profile76_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,3] 2 profile76_node12_cert).mp (by decide +kernel))

def profile76_node13_cert : CutBound 5 := { lost := (rows 0 4 2 2 12), upper := (rows 15 27 29 13 19), lower := (rows 15 27 29 13 16), losses := [{ target := 1, region := (rows 1 0 6 15 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 15 0 8 31), good := (rows 27 27 27 27 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 21 16) }] }

theorem profile76_node13 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,5] 2 profile76_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25,5] 2 profile76_node13_cert).mp (by decide +kernel))

def profile76_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node11 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25] 2 (by decide) (choices 2) [3,5] profile76_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25,25] (choices 2) [3,5] profile76_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node12
  · exact profile76_node13

def profile76_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node8 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25] 2 (by decide) (choices 3) [11,19,25] profile76_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14,25] (choices 3) [11,19,25] profile76_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node9
  · exact profile76_node10
  · exact profile76_node11

def profile76_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node1 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14] 2 (by decide) (choices 3) [13,21,25] profile76_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [14] (choices 3) [13,21,25] profile76_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node2
  · exact profile76_node5
  · exact profile76_node8

def profile76_node16_cert : CutBound 5 := { lost := (rows 0 16 16 6 6), upper := (rows 23 15 15 25 25), lower := (rows 23 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile76_node16 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,11] 2 profile76_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,11] 2 profile76_node16_cert).mp (by decide +kernel))

def profile76_node18_cert : CutBound 5 := { lost := (rows 0 16 2 20 6), upper := (rows 23 15 29 11 25), lower := (rows 23 15 29 11 16), losses := [{ target := 1, region := (rows 1 0 14 8 30), good := (rows 21 29 29 29 16) },{ target := 2, region := (rows 1 2 0 11 31), good := (rows 27 27 25 27 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile76_node18 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25,3] 2 profile76_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25,3] 2 profile76_node18_cert).mp (by decide +kernel))

def profile76_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node17 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25] 2 (by decide) (choices 2) [3] profile76_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13,25] (choices 2) [3] profile76_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node18

def profile76_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node15 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13] 2 (by decide) (choices 3) [11,25] profile76_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,13] (choices 3) [11,25] profile76_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node16
  · exact profile76_node17

def profile76_node21_cert : CutBound 5 := { lost := (rows 0 4 16 18 6), upper := (rows 23 27 15 13 25), lower := (rows 23 27 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 31), good := (rows 29 25 29 29 16) },{ target := 2, region := (rows 1 14 0 8 30), good := (rows 19 27 27 27 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile76_node21 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11,5] 2 profile76_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11,5] 2 profile76_node21_cert).mp (by decide +kernel))

def profile76_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node20 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11] 2 (by decide) (choices 2) [5] profile76_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25,11] (choices 2) [5] profile76_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node21

def profile76_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node19 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25] 2 (by decide) (choices 3) [11] profile76_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22,25] (choices 3) [11] profile76_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node20

def profile76_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node14 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22] 2 (by decide) (choices 3) [13,25] profile76_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [22] (choices 3) [13,25] profile76_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node15
  · exact profile76_node19

def profile76_node24_cert : CutBound 5 := { lost := (rows 0 16 16 2 10), upper := (rows 27 15 15 29 21), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node24 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,11] 2 profile76_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,11] 2 profile76_node24_cert).mp (by decide +kernel))

def profile76_node25_cert : CutBound 5 := { lost := (rows 0 16 8 18 2), upper := (rows 27 15 23 13 29), lower := (rows 27 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile76_node25 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,19] 2 profile76_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,19] 2 profile76_node25_cert).mp (by decide +kernel))

def profile76_node27_cert : CutBound 5 := { lost := (rows 0 16 2 20 10), upper := (rows 27 15 29 11 21), lower := (rows 27 15 29 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 25 11 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 19 23 21 19 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 11 0) }] }

theorem profile76_node27 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,3] 2 profile76_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,3] 2 profile76_node27_cert).mp (by decide +kernel))

def profile76_node28_cert : CutBound 5 := { lost := (rows 4 0 2 2 12), upper := (rows 27 15 29 13 19), lower := (rows 27 15 29 13 16), losses := [{ target := 1, region := (rows 1 0 5 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 21 21 16) }] }

theorem profile76_node28 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,5] 2 profile76_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25,5] 2 profile76_node28_cert).mp (by decide +kernel))

def profile76_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node26 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25] 2 (by decide) (choices 2) [3,5] profile76_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13,25] (choices 2) [3,5] profile76_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node27
  · exact profile76_node28

def profile76_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node23 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13] 2 (by decide) (choices 3) [11,19,25] profile76_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,13] (choices 3) [11,19,25] profile76_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node24
  · exact profile76_node25
  · exact profile76_node26

def profile76_node31_cert : CutBound 5 := { lost := (rows 4 0 16 18 6), upper := (rows 27 23 15 13 25), lower := (rows 27 23 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 14 31), good := (rows 25 29 29 29 16) },{ target := 2, region := (rows 5 2 0 8 29), good := (rows 27 19 27 25 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile76_node31 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11,5] 2 profile76_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11,5] 2 profile76_node31_cert).mp (by decide +kernel))

def profile76_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node30 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11] 2 (by decide) (choices 2) [5] profile76_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21,11] (choices 2) [5] profile76_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node31

def profile76_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node29 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21] 2 (by decide) (choices 3) [11] profile76_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,21] (choices 3) [11] profile76_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node30

def profile76_node33_cert : CutBound 5 := { lost := (rows 4 4 0 2 10), upper := (rows 27 27 15 13 21), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 19 23 0 16) }] }

theorem profile76_node33 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25,11] 2 profile76_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25,11] 2 profile76_node33_cert).mp (by decide +kernel))

def profile76_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node32 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25] 2 (by decide) (choices 3) [11] profile76_node32_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26,25] (choices 3) [11] profile76_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node33

def profile76_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node22 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26] 2 (by decide) (choices 3) [13,21,25] profile76_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [26] (choices 3) [13,21,25] profile76_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node23
  · exact profile76_node29
  · exact profile76_node32

def profile76_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile76_node0 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [] 2 (by decide) (choices 3) [14,22,26] profile76_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [] (choices 3) [14,22,26] profile76_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node1
  · exact profile76_node14
  · exact profile76_node22

theorem profile76 : Upper (D (n:=5) [52,50,50,35,34]) (R (n:=5) [52,50,50,35,34]) [] 2 := profile76_node0

def profile77_node4_cert : CutBound 5 := { lost := (rows 16 16 0 6 5), upper := (rows 15 15 23 25 26), lower := (rows 15 15 23 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 24 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 25 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 25 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 11 0) }] }

theorem profile77_node4 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,17] 2 profile77_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,17] 2 profile77_node4_cert).mp (by decide +kernel))

def profile77_node5_cert : CutBound 5 := { lost := (rows 16 16 0 5 6), upper := (rows 15 15 23 26 25), lower := (rows 15 15 23 26 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 30 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 24 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 26 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 11 0) }] }

theorem profile77_node5 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,18] 2 profile77_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19,18] 2 profile77_node5_cert).mp (by decide +kernel))

def profile77_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node3 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19] 2 (by decide) (choices 2) [17,18] profile77_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,19] (choices 2) [17,18] profile77_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node4
  · exact profile77_node5

def profile77_node6_cert : CutBound 5 := { lost := (rows 16 16 0 4 12), upper := (rows 15 15 29 27 19), lower := (rows 15 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node6 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,25] 2 profile77_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,25] 2 profile77_node6_cert).mp (by decide +kernel))

def profile77_node7_cert : CutBound 5 := { lost := (rows 16 16 0 4 12), upper := (rows 15 15 30 27 19), lower := (rows 15 15 30 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node7 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,26] 2 profile77_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13,26] 2 profile77_node7_cert).mp (by decide +kernel))

def profile77_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node2 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13] 2 (by decide) (choices 3) [19,25,26] profile77_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,13] (choices 3) [19,25,26] profile77_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node3
  · exact profile77_node6
  · exact profile77_node7

def profile77_node10_cert : CutBound 5 := { lost := (rows 16 0 16 6 5), upper := (rows 15 23 15 25 26), lower := (rows 15 23 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 24 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 13 25 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 25 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 13 0) }] }

theorem profile77_node10 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,17] 2 profile77_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,17] 2 profile77_node10_cert).mp (by decide +kernel))

def profile77_node11_cert : CutBound 5 := { lost := (rows 16 0 16 5 6), upper := (rows 15 23 15 26 25), lower := (rows 15 23 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 26 16) },{ target := 4, region := (rows 13 2 13 8 0), good := (rows 15 7 15 15 0) }] }

theorem profile77_node11 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,18] 2 profile77_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11,18] 2 profile77_node11_cert).mp (by decide +kernel))

def profile77_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node9 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11] 2 (by decide) (choices 2) [17,18] profile77_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,11] (choices 2) [17,18] profile77_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node10
  · exact profile77_node11

def profile77_node12_cert : CutBound 5 := { lost := (rows 16 8 0 20 4), upper := (rows 15 23 29 11 27), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile77_node12 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,25] 2 profile77_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,25] 2 profile77_node12_cert).mp (by decide +kernel))

def profile77_node14_cert : CutBound 5 := { lost := (rows 16 0 0 20 6), upper := (rows 15 23 30 11 25), lower := (rows 15 23 30 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 25), good := (rows 29 21 28 25 16) },{ target := 2, region := (rows 1 2 0 11 27), good := (rows 27 27 26 27 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile77_node14 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26,3] 2 profile77_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26,3] 2 profile77_node14_cert).mp (by decide +kernel))

def profile77_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node13 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26] 2 (by decide) (choices 2) [3] profile77_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21,26] (choices 2) [3] profile77_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node14

def profile77_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node8 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21] 2 (by decide) (choices 3) [11,25,26] profile77_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,21] (choices 3) [11,25,26] profile77_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node9
  · exact profile77_node12
  · exact profile77_node13

def profile77_node17_cert : CutBound 5 := { lost := (rows 0 4 0 6 9), upper := (rows 15 27 15 25 22), lower := (rows 15 27 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 24 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 25 13 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 11 27 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 17 16) }] }

theorem profile77_node17 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,17] 2 profile77_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,17] 2 profile77_node17_cert).mp (by decide +kernel))

def profile77_node18_cert : CutBound 5 := { lost := (rows 16 0 16 5 10), upper := (rows 15 27 15 26 21), lower := (rows 15 27 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 26 14 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 26 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 18 16) },{ target := 4, region := (rows 15 2 15 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile77_node18 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,18] 2 profile77_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,18] 2 profile77_node18_cert).mp (by decide +kernel))

def profile77_node19_cert : CutBound 5 := { lost := (rows 16 4 16 0 12), upper := (rows 15 27 15 28 19), lower := (rows 15 27 15 28 16), losses := [{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 19 23 20 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 13 0) }] }

theorem profile77_node19 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,20] 2 profile77_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11,20] 2 profile77_node19_cert).mp (by decide +kernel))

def profile77_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node16 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11] 2 (by decide) (choices 2) [17,18,20] profile77_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,11] (choices 2) [17,18,20] profile77_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node17
  · exact profile77_node18
  · exact profile77_node19

def profile77_node21_cert : CutBound 5 := { lost := (rows 0 4 8 4 3), upper := (rows 15 27 23 11 28), lower := (rows 15 27 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 26 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 25 21 25 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile77_node21 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,3] 2 profile77_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,3] 2 profile77_node21_cert).mp (by decide +kernel))

def profile77_node22_cert : CutBound 5 := { lost := (rows 0 4 8 2 5), upper := (rows 15 27 23 13 26), lower := (rows 15 27 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 26 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 29 13 16) },{ target := 2, region := (rows 1 11 0 8 27), good := (rows 27 27 19 27 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 5 16) }] }

theorem profile77_node22 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,5] 2 profile77_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,5] 2 profile77_node22_cert).mp (by decide +kernel))

def profile77_node23_cert : CutBound 5 := { lost := (rows 0 4 8 1 6), upper := (rows 15 27 23 14 25), lower := (rows 15 27 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 25 21 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 27 19 26 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 6 16) }] }

theorem profile77_node23 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,6] 2 profile77_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19,6] 2 profile77_node23_cert).mp (by decide +kernel))

def profile77_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node20 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19] 2 (by decide) (choices 2) [3,5,6] profile77_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,19] (choices 2) [3,5,6] profile77_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node21
  · exact profile77_node22
  · exact profile77_node23

def profile77_node25_cert : CutBound 5 := { lost := (rows 0 4 2 4 9), upper := (rows 15 27 29 11 22), lower := (rows 15 27 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 19 16) }] }

theorem profile77_node25 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,3] 2 profile77_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,3] 2 profile77_node25_cert).mp (by decide +kernel))

def profile77_node26_cert : CutBound 5 := { lost := (rows 0 4 2 1 12), upper := (rows 15 27 29 14 19), lower := (rows 15 27 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 28 14 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 12 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 22 16) }] }

theorem profile77_node26 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,6] 2 profile77_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25,6] 2 profile77_node26_cert).mp (by decide +kernel))

def profile77_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node24 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25] 2 (by decide) (choices 2) [3,6] profile77_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,25] (choices 2) [3,6] profile77_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node25
  · exact profile77_node26

def profile77_node28_cert : CutBound 5 := { lost := (rows 16 0 1 20 10), upper := (rows 15 27 30 11 21), lower := (rows 15 27 30 11 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 26 11 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 22 19 16) },{ target := 4, region := (rows 5 2 4 15 0), good := (rows 15 11 15 11 0) }] }

theorem profile77_node28 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,3] 2 profile77_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,3] 2 profile77_node28_cert).mp (by decide +kernel))

def profile77_node29_cert : CutBound 5 := { lost := (rows 0 4 1 2 12), upper := (rows 15 27 30 13 19), lower := (rows 15 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 12 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 13 25 28 13 16) },{ target := 2, region := (rows 1 11 0 8 27), good := (rows 27 27 26 27 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 22 21 16) }] }

theorem profile77_node29 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,5] 2 profile77_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26,5] 2 profile77_node29_cert).mp (by decide +kernel))

def profile77_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node27 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26] 2 (by decide) (choices 2) [3,5] profile77_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25,26] (choices 2) [3,5] profile77_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node28
  · exact profile77_node29

def profile77_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node15 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25] 2 (by decide) (choices 3) [11,19,25,26] profile77_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,25] (choices 3) [11,19,25,26] profile77_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node16
  · exact profile77_node20
  · exact profile77_node24
  · exact profile77_node27

def profile77_node31_cert : CutBound 5 := { lost := (rows 16 0 16 4 12), upper := (rows 15 30 15 27 19), lower := (rows 15 30 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node31 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,11] 2 profile77_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,11] 2 profile77_node31_cert).mp (by decide +kernel))

def profile77_node33_cert : CutBound 5 := { lost := (rows 16 0 0 20 6), upper := (rows 15 30 23 11 25), lower := (rows 15 30 23 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 25), good := (rows 29 28 21 25 16) },{ target := 2, region := (rows 1 2 0 13 29), good := (rows 27 26 27 27 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile77_node33 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19,3] 2 profile77_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19,3] 2 profile77_node33_cert).mp (by decide +kernel))

def profile77_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node32 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19] 2 (by decide) (choices 2) [3] profile77_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,19] (choices 2) [3] profile77_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node33

def profile77_node34_cert : CutBound 5 := { lost := (rows 16 1 0 20 12), upper := (rows 15 30 29 11 19), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile77_node34 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,25] 2 profile77_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28,25] 2 profile77_node34_cert).mp (by decide +kernel))

def profile77_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node30 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28] 2 (by decide) (choices 3) [11,19,25] profile77_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14,28] (choices 3) [11,19,25] profile77_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node31
  · exact profile77_node32
  · exact profile77_node34

def profile77_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node1 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile77_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [14] (choices 3) [13,21,25,28] profile77_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node2
  · exact profile77_node8
  · exact profile77_node15
  · exact profile77_node30

def profile77_node38_cert : CutBound 5 := { lost := (rows 0 16 16 6 5), upper := (rows 23 15 15 25 26), lower := (rows 23 15 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 30 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 25 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 25 16) },{ target := 4, region := (rows 1 14 14 8 0), good := (rows 7 15 15 15 0) }] }

theorem profile77_node38 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,17] 2 profile77_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,17] 2 profile77_node38_cert).mp (by decide +kernel))

def profile77_node39_cert : CutBound 5 := { lost := (rows 0 16 16 5 6), upper := (rows 23 15 15 26 25), lower := (rows 23 15 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 26 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 29 29 24 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 26 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 14 0) }] }

theorem profile77_node39 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,18] 2 profile77_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11,18] 2 profile77_node39_cert).mp (by decide +kernel))

def profile77_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node37 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11] 2 (by decide) (choices 2) [17,18] profile77_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,11] (choices 2) [17,18] profile77_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node38
  · exact profile77_node39

def profile77_node41_cert : CutBound 5 := { lost := (rows 0 16 0 20 5), upper := (rows 23 15 29 11 26), lower := (rows 23 15 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 26), good := (rows 22 30 28 26 16) },{ target := 2, region := (rows 1 2 0 11 27), good := (rows 27 27 25 27 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile77_node41 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25,3] 2 profile77_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25,3] 2 profile77_node41_cert).mp (by decide +kernel))

def profile77_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node40 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25] 2 (by decide) (choices 2) [3] profile77_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,25] (choices 2) [3] profile77_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node41

def profile77_node42_cert : CutBound 5 := { lost := (rows 8 16 0 20 4), upper := (rows 23 15 30 11 27), lower := (rows 23 15 30 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile77_node42 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,26] 2 profile77_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13,26] 2 profile77_node42_cert).mp (by decide +kernel))

def profile77_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node36 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13] 2 (by decide) (choices 3) [11,25,26] profile77_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,13] (choices 3) [11,25,26] profile77_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node37
  · exact profile77_node40
  · exact profile77_node42

def profile77_node45_cert : CutBound 5 := { lost := (rows 0 4 16 20 3), upper := (rows 23 27 15 11 28), lower := (rows 23 27 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 26 30 10 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 25 29 9 16) },{ target := 2, region := (rows 1 3 0 15 16), good := (rows 27 27 11 11 16) },{ target := 4, region := (rows 1 2 15 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile77_node45 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,3] 2 profile77_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,3] 2 profile77_node45_cert).mp (by decide +kernel))

def profile77_node46_cert : CutBound 5 := { lost := (rows 0 4 16 18 5), upper := (rows 23 27 15 13 26), lower := (rows 23 27 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 25 13 13 16) },{ target := 2, region := (rows 1 14 0 8 30), good := (rows 19 27 27 27 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile77_node46 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,5] 2 profile77_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,5] 2 profile77_node46_cert).mp (by decide +kernel))

def profile77_node47_cert : CutBound 5 := { lost := (rows 0 4 16 17 6), upper := (rows 23 27 15 14 25), lower := (rows 23 27 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 25 29 28 16) },{ target := 2, region := (rows 1 6 0 8 22), good := (rows 19 27 27 26 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 14 0) }] }

theorem profile77_node47 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,6] 2 profile77_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11,6] 2 profile77_node47_cert).mp (by decide +kernel))

def profile77_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node44 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11] 2 (by decide) (choices 2) [3,5,6] profile77_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25,11] (choices 2) [3,5,6] profile77_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node45
  · exact profile77_node46
  · exact profile77_node47

def profile77_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node43 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25] 2 (by decide) (choices 3) [11] profile77_node43_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,25] (choices 3) [11] profile77_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node44

def profile77_node48_cert : CutBound 5 := { lost := (rows 8 0 16 20 4), upper := (rows 23 30 15 11 27), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile77_node48 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,28] 2 profile77_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22,28] 2 profile77_node48_cert).mp (by decide +kernel))

def profile77_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node35 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22] 2 (by decide) (choices 3) [13,25,28] profile77_node35_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [22] (choices 3) [13,25,28] profile77_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node36
  · exact profile77_node43
  · exact profile77_node48

def profile77_node52_cert : CutBound 5 := { lost := (rows 0 16 16 6 9), upper := (rows 27 15 15 25 22), lower := (rows 27 15 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 30 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 25 13 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 25 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 19 23 23 17 16) },{ target := 4, region := (rows 1 15 15 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile77_node52 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,17] 2 profile77_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,17] 2 profile77_node52_cert).mp (by decide +kernel))

def profile77_node53_cert : CutBound 5 := { lost := (rows 4 0 0 5 10), upper := (rows 27 15 15 26 21), lower := (rows 27 15 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 26 14 14 26 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 29 24 16) },{ target := 2, region := (rows 9 2 0 9 16), good := (rows 27 11 11 27 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 19 23 23 18 16) }] }

theorem profile77_node53 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,18] 2 profile77_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,18] 2 profile77_node53_cert).mp (by decide +kernel))

def profile77_node54_cert : CutBound 5 := { lost := (rows 4 16 16 0 12), upper := (rows 27 15 15 28 19), lower := (rows 27 15 15 28 16), losses := [{ target := 2, region := (rows 7 2 0 8 23), good := (rows 27 27 27 25 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 19 23 23 20 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 14 0) }] }

theorem profile77_node54 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,20] 2 profile77_node54_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11,20] 2 profile77_node54_cert).mp (by decide +kernel))

def profile77_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node51 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11] 2 (by decide) (choices 2) [17,18,20] profile77_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,11] (choices 2) [17,18,20] profile77_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node52
  · exact profile77_node53
  · exact profile77_node54

def profile77_node56_cert : CutBound 5 := { lost := (rows 4 0 8 4 3), upper := (rows 27 15 23 11 28), lower := (rows 27 15 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 25 29 21 25 16) },{ target := 2, region := (rows 5 2 0 15 16), good := (rows 27 11 27 11 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 7 16) }] }

theorem profile77_node56 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,3] 2 profile77_node56_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,3] 2 profile77_node56_cert).mp (by decide +kernel))

def profile77_node57_cert : CutBound 5 := { lost := (rows 4 0 8 2 5), upper := (rows 27 15 23 13 26), lower := (rows 27 15 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 26 30 22 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 29 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 19 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 5 16) }] }

theorem profile77_node57 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,5] 2 profile77_node57_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,5] 2 profile77_node57_cert).mp (by decide +kernel))

def profile77_node58_cert : CutBound 5 := { lost := (rows 4 0 8 1 6), upper := (rows 27 15 23 14 25), lower := (rows 27 15 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 25 29 21 28 16) },{ target := 2, region := (rows 11 2 0 8 27), good := (rows 27 27 19 27 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 6 16) }] }

theorem profile77_node58 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,6] 2 profile77_node58_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19,6] 2 profile77_node58_cert).mp (by decide +kernel))

def profile77_node55_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node55 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19] 2 (by decide) (choices 2) [3,5,6] profile77_node55_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,19] (choices 2) [3,5,6] profile77_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node56
  · exact profile77_node57
  · exact profile77_node58

def profile77_node60_cert : CutBound 5 := { lost := (rows 0 16 2 20 9), upper := (rows 27 15 29 11 22), lower := (rows 27 15 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 30 28 26 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 25 11 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 21 19 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 11 0) }] }

theorem profile77_node60 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,3] 2 profile77_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,3] 2 profile77_node60_cert).mp (by decide +kernel))

def profile77_node61_cert : CutBound 5 := { lost := (rows 4 0 2 1 12), upper := (rows 27 15 29 14 19), lower := (rows 27 15 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 26 14 28 14 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 12 16) },{ target := 2, region := (rows 11 2 0 8 27), good := (rows 27 27 25 27 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 21 22 16) }] }

theorem profile77_node61 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,6] 2 profile77_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25,6] 2 profile77_node61_cert).mp (by decide +kernel))

def profile77_node59_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node59 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25] 2 (by decide) (choices 2) [3,6] profile77_node59_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,25] (choices 2) [3,6] profile77_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node60
  · exact profile77_node61

def profile77_node63_cert : CutBound 5 := { lost := (rows 4 0 1 4 10), upper := (rows 27 15 30 11 21), lower := (rows 27 15 30 11 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 25 29 28 25 16) },{ target := 2, region := (rows 5 2 0 15 16), good := (rows 27 11 27 11 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 22 19 16) }] }

theorem profile77_node63 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,3] 2 profile77_node63_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,3] 2 profile77_node63_cert).mp (by decide +kernel))

def profile77_node64_cert : CutBound 5 := { lost := (rows 4 0 1 2 12), upper := (rows 27 15 30 13 19), lower := (rows 27 15 30 13 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 12 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 25 13 28 13 16) },{ target := 2, region := (rows 7 2 0 8 23), good := (rows 27 27 27 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 19 23 22 21 16) }] }

theorem profile77_node64 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,5] 2 profile77_node64_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26,5] 2 profile77_node64_cert).mp (by decide +kernel))

def profile77_node62_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node62 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26] 2 (by decide) (choices 2) [3,5] profile77_node62_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13,26] (choices 2) [3,5] profile77_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node63
  · exact profile77_node64

def profile77_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node50 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13] 2 (by decide) (choices 3) [11,19,25,26] profile77_node50_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,13] (choices 3) [11,19,25,26] profile77_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node51
  · exact profile77_node55
  · exact profile77_node59
  · exact profile77_node62

def profile77_node67_cert : CutBound 5 := { lost := (rows 4 0 16 20 3), upper := (rows 27 23 15 11 28), lower := (rows 27 23 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 26 22 30 10 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 25 21 29 9 16) },{ target := 2, region := (rows 3 2 0 15 16), good := (rows 27 27 11 11 16) },{ target := 4, region := (rows 1 2 15 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile77_node67 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,3] 2 profile77_node67_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,3] 2 profile77_node67_cert).mp (by decide +kernel))

def profile77_node68_cert : CutBound 5 := { lost := (rows 4 0 16 18 5), upper := (rows 27 23 15 13 26), lower := (rows 27 23 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 26 22 30 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 29 13 13 16) },{ target := 2, region := (rows 5 2 0 8 21), good := (rows 27 19 27 25 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 13 0) }] }

theorem profile77_node68 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,5] 2 profile77_node68_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,5] 2 profile77_node68_cert).mp (by decide +kernel))

def profile77_node69_cert : CutBound 5 := { lost := (rows 4 0 16 17 6), upper := (rows 27 23 15 14 25), lower := (rows 27 23 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 25 21 29 28 16) },{ target := 2, region := (rows 13 2 0 8 29), good := (rows 27 19 27 27 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 14 0) }] }

theorem profile77_node69 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,6] 2 profile77_node69_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11,6] 2 profile77_node69_cert).mp (by decide +kernel))

def profile77_node66_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node66 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11] 2 (by decide) (choices 2) [3,5,6] profile77_node66_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21,11] (choices 2) [3,5,6] profile77_node66_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node67
  · exact profile77_node68
  · exact profile77_node69

def profile77_node65_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node65 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21] 2 (by decide) (choices 3) [11] profile77_node65_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,21] (choices 3) [11] profile77_node65_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node66

def profile77_node71_cert : CutBound 5 := { lost := (rows 4 4 16 16 8), upper := (rows 27 27 15 15 23), lower := (rows 27 27 15 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node71 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25,11] 2 profile77_node71_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25,11] 2 profile77_node71_cert).mp (by decide +kernel))

def profile77_node70_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node70 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25] 2 (by decide) (choices 3) [11] profile77_node70_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,25] (choices 3) [11] profile77_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node71

def profile77_node74_cert : CutBound 5 := { lost := (rows 4 0 16 20 10), upper := (rows 27 30 15 11 21), lower := (rows 27 30 15 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 20), good := (rows 25 28 29 9 16) },{ target := 2, region := (rows 3 2 0 15 16), good := (rows 27 27 11 11 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 19 22 23 3 16) },{ target := 4, region := (rows 1 2 13 13 0), good := (rows 15 14 15 15 0) }] }

theorem profile77_node74 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,3] 2 profile77_node74_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,3] 2 profile77_node74_cert).mp (by decide +kernel))

def profile77_node75_cert : CutBound 5 := { lost := (rows 4 0 16 18 12), upper := (rows 27 30 15 13 19), lower := (rows 27 30 15 13 16), losses := [{ target := 1, region := (rows 1 0 4 12 16), good := (rows 25 28 13 13 16) },{ target := 2, region := (rows 7 2 0 8 23), good := (rows 27 27 27 25 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 19 22 23 21 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 13 0) }] }

theorem profile77_node75 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,5] 2 profile77_node75_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11,5] 2 profile77_node75_cert).mp (by decide +kernel))

def profile77_node73_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node73 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11] 2 (by decide) (choices 2) [3,5] profile77_node73_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28,11] (choices 2) [3,5] profile77_node73_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node74
  · exact profile77_node75

def profile77_node72_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node72 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28] 2 (by decide) (choices 3) [11] profile77_node72_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26,28] (choices 3) [11] profile77_node72_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node73

def profile77_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node49 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile77_node49_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [26] (choices 3) [13,21,25,28] profile77_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node50
  · exact profile77_node65
  · exact profile77_node70
  · exact profile77_node72

def profile77_node78_cert : CutBound 5 := { lost := (rows 0 16 16 4 12), upper := (rows 29 15 15 27 19), lower := (rows 29 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node78 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,11] 2 profile77_node78_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,11] 2 profile77_node78_cert).mp (by decide +kernel))

def profile77_node80_cert : CutBound 5 := { lost := (rows 0 16 0 20 5), upper := (rows 29 15 23 11 26), lower := (rows 29 15 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 26), good := (rows 28 30 22 26 16) },{ target := 2, region := (rows 1 2 0 14 30), good := (rows 25 27 27 27 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile77_node80 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19,3] 2 profile77_node80_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19,3] 2 profile77_node80_cert).mp (by decide +kernel))

def profile77_node79_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node79 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19] 2 (by decide) (choices 2) [3] profile77_node79_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,19] (choices 2) [3] profile77_node79_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node80

def profile77_node81_cert : CutBound 5 := { lost := (rows 2 16 0 20 12), upper := (rows 29 15 30 11 19), lower := (rows 29 15 30 8 16), losses := [{ target := 1, region := (rows 5 0 4 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile77_node81 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,26] 2 profile77_node81_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13,26] 2 profile77_node81_cert).mp (by decide +kernel))

def profile77_node77_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node77 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13] 2 (by decide) (choices 3) [11,19,26] profile77_node77_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,13] (choices 3) [11,19,26] profile77_node77_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node78
  · exact profile77_node79
  · exact profile77_node81

def profile77_node82_cert : CutBound 5 := { lost := (rows 0 8 16 20 4), upper := (rows 29 23 15 11 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile77_node82 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,21] 2 profile77_node82_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,21] 2 profile77_node82_cert).mp (by decide +kernel))

def profile77_node85_cert : CutBound 5 := { lost := (rows 0 4 16 20 9), upper := (rows 29 27 15 11 22), lower := (rows 29 27 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 28 26 30 10 16) },{ target := 2, region := (rows 1 3 0 15 16), good := (rows 27 27 11 11 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 21 19 23 3 16) },{ target := 4, region := (rows 1 2 14 14 0), good := (rows 13 15 15 15 0) }] }

theorem profile77_node85 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,3] 2 profile77_node85_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,3] 2 profile77_node85_cert).mp (by decide +kernel))

def profile77_node86_cert : CutBound 5 := { lost := (rows 0 4 16 17 12), upper := (rows 29 27 15 14 19), lower := (rows 29 27 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 28 26 14 14 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 19 23 22 16) },{ target := 4, region := (rows 1 2 6 14 0), good := (rows 13 15 15 14 0) }] }

theorem profile77_node86 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,6] 2 profile77_node86_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11,6] 2 profile77_node86_cert).mp (by decide +kernel))

def profile77_node84_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node84 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11] 2 (by decide) (choices 2) [3,6] profile77_node84_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25,11] (choices 2) [3,6] profile77_node84_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node85
  · exact profile77_node86

def profile77_node83_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node83 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25] 2 (by decide) (choices 3) [11] profile77_node83_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,25] (choices 3) [11] profile77_node83_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node84

def profile77_node88_cert : CutBound 5 := { lost := (rows 2 1 0 4 12), upper := (rows 29 30 15 11 19), lower := (rows 29 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 13 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 21 22 23 0 16) }] }

theorem profile77_node88 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28,11] 2 profile77_node88_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28,11] 2 profile77_node88_cert).mp (by decide +kernel))

def profile77_node87_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node87 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28] 2 (by decide) (choices 3) [11] profile77_node87_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28,28] (choices 3) [11] profile77_node87_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node88

def profile77_node76_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node76 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28] 2 (by decide) (choices 3) [13,21,25,28] profile77_node76_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [28] (choices 3) [13,21,25,28] profile77_node76_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node77
  · exact profile77_node82
  · exact profile77_node83
  · exact profile77_node87

def profile77_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node0 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [] 2 (by decide) (choices 3) [14,22,26,28] profile77_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [] (choices 3) [14,22,26,28] profile77_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node1
  · exact profile77_node35
  · exact profile77_node49
  · exact profile77_node76

theorem profile77 : Upper (D (n:=5) [51,51,50,35,34]) (R (n:=5) [51,51,50,35,34]) [] 2 := profile77_node0

def profile78_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 13 28 28), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile78_node3 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,9] 2 profile78_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,9] 2 profile78_node3_cert).mp (by decide +kernel))

def profile78_node4_cert : CutBound 5 := { lost := (rows 0 16 1 16 0), upper := (rows 31 15 28 13 29), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile78_node4 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,24] 2 profile78_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13,24] 2 profile78_node4_cert).mp (by decide +kernel))

def profile78_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node2 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13] 2 (by decide) (choices 2) [9,24] profile78_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,13] (choices 2) [9,24] profile78_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node3
  · exact profile78_node4

def profile78_node5_cert : CutBound 5 := { lost := (rows 0 1 16 16 0), upper := (rows 31 30 13 13 29), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile78_node5 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,28] 2 profile78_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30,28] 2 profile78_node5_cert).mp (by decide +kernel))

def profile78_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node1 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30] 2 (by decide) (choices 3) [13,28] profile78_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [30] (choices 3) [13,28] profile78_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node2
  · exact profile78_node5

def profile78_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node0 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [] 2 (by decide) (choices 4) [30] profile78_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [] (choices 4) [30] profile78_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node1

theorem profile78 : Upper (D (n:=5) [66,49,36,36,34]) (R (n:=5) [66,49,36,36,34]) [] 2 := profile78_node0

def profile79_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 15 14 28 28), lower := (rows 31 15 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 28 8 16) }] }

theorem profile79_node3 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,10] 2 profile79_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,10] 2 profile79_node3_cert).mp (by decide +kernel))

def profile79_node4_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 31 15 28 14 30), lower := (rows 31 15 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile79_node4 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,24] 2 profile79_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13,24] 2 profile79_node4_cert).mp (by decide +kernel))

def profile79_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node2 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13] 2 (by decide) (choices 2) [10,24] profile79_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,13] (choices 2) [10,24] profile79_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node3
  · exact profile79_node4

def profile79_node5_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile79_node5 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,28] 2 profile79_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30,28] 2 profile79_node5_cert).mp (by decide +kernel))

def profile79_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node1 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30] 2 (by decide) (choices 3) [13,28] profile79_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [30] (choices 3) [13,28] profile79_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node2
  · exact profile79_node5

def profile79_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node0 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [] 2 (by decide) (choices 4) [30] profile79_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [] (choices 4) [30] profile79_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node1

theorem profile79 : Upper (D (n:=5) [65,50,36,36,34]) (R (n:=5) [65,50,36,36,34]) [] 2 := profile79_node0

def profile80_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 15 27 15 25 25), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile80_node3 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,11] 2 profile80_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,11] 2 profile80_node3_cert).mp (by decide +kernel))

def profile80_node4_cert : CutBound 5 := { lost := (rows 0 0 2 16 0), upper := (rows 15 27 29 11 27), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 11 13 8 0) }] }

theorem profile80_node4 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,25] 2 profile80_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25,25] 2 profile80_node4_cert).mp (by decide +kernel))

def profile80_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node2 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25] 2 (by decide) (choices 3) [11,25] profile80_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14,25] (choices 3) [11,25] profile80_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile80_node3
  · exact profile80_node4

def profile80_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node1 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14] 2 (by decide) (choices 3) [25] profile80_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [14] (choices 3) [25] profile80_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node2

def profile80_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 15 15 25 25), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile80_node7 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,11] 2 profile80_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,11] 2 profile80_node7_cert).mp (by decide +kernel))

def profile80_node8_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 27 15 29 11 27), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 8 0) }] }

theorem profile80_node8 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,25] 2 profile80_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13,25] 2 profile80_node8_cert).mp (by decide +kernel))

def profile80_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node6 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13] 2 (by decide) (choices 3) [11,25] profile80_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,13] (choices 3) [11,25] profile80_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile80_node7
  · exact profile80_node8

def profile80_node9_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile80_node9 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,25] 2 profile80_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26,25] 2 profile80_node9_cert).mp (by decide +kernel))

def profile80_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node5 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26] 2 (by decide) (choices 3) [13,25] profile80_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [26] (choices 3) [13,25] profile80_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile80_node6
  · exact profile80_node9

def profile80_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile80_node11 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28,25] 2 profile80_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28,25] 2 profile80_node11_cert).mp (by decide +kernel))

def profile80_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node10 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28] 2 (by decide) (choices 3) [25] profile80_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [28] (choices 3) [25] profile80_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node11

def profile80_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node0 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [] 2 (by decide) (choices 3) [14,26,28] profile80_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [] (choices 3) [14,26,28] profile80_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile80_node1
  · exact profile80_node5
  · exact profile80_node10

theorem profile80 : Upper (D (n:=5) [52,50,49,36,34]) (R (n:=5) [52,50,49,36,34]) [] 2 := profile80_node0

def profile81_node3_cert : CutBound 5 := { lost := (rows 16 0 16 0 0), upper := (rows 15 27 15 27 27), lower := (rows 15 27 15 8 16), losses := [{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile81_node3 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,11] 2 profile81_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,11] 2 profile81_node3_cert).mp (by decide +kernel))

def profile81_node4_cert : CutBound 5 := { lost := (rows 0 0 2 16 0), upper := (rows 15 27 29 11 27), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 11 13 8 0) }] }

theorem profile81_node4 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,25] 2 profile81_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,25] 2 profile81_node4_cert).mp (by decide +kernel))

def profile81_node5_cert : CutBound 5 := { lost := (rows 16 0 1 16 0), upper := (rows 15 27 30 11 27), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 4, region := (rows 5 2 4 15 0), good := (rows 15 11 15 8 0) }] }

theorem profile81_node5 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,26] 2 profile81_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25,26] 2 profile81_node5_cert).mp (by decide +kernel))

def profile81_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node2 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25] 2 (by decide) (choices 3) [11,25,26] profile81_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14,25] (choices 3) [11,25,26] profile81_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile81_node3
  · exact profile81_node4
  · exact profile81_node5

def profile81_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node1 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14] 2 (by decide) (choices 3) [25] profile81_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [14] (choices 3) [25] profile81_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile81_node2

def profile81_node8_cert : CutBound 5 := { lost := (rows 0 16 16 0 0), upper := (rows 27 15 15 27 27), lower := (rows 27 15 15 8 16), losses := [{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile81_node8 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,11] 2 profile81_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,11] 2 profile81_node8_cert).mp (by decide +kernel))

def profile81_node9_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 27 15 29 11 27), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 15 0), good := (rows 11 15 15 8 0) }] }

theorem profile81_node9 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,25] 2 profile81_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,25] 2 profile81_node9_cert).mp (by decide +kernel))

def profile81_node10_cert : CutBound 5 := { lost := (rows 0 0 1 16 0), upper := (rows 27 15 30 11 27), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 11 15 14 8 0) }] }

theorem profile81_node10 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,26] 2 profile81_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13,26] 2 profile81_node10_cert).mp (by decide +kernel))

def profile81_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node7 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13] 2 (by decide) (choices 3) [11,25,26] profile81_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,13] (choices 3) [11,25,26] profile81_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile81_node8
  · exact profile81_node9
  · exact profile81_node10

def profile81_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile81_node11 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,25] 2 profile81_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,25] 2 profile81_node11_cert).mp (by decide +kernel))

def profile81_node12_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 30 15 11 27), lower := (rows 27 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile81_node12 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,28] 2 profile81_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26,28] 2 profile81_node12_cert).mp (by decide +kernel))

def profile81_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node6 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26] 2 (by decide) (choices 3) [13,25,28] profile81_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [26] (choices 3) [13,25,28] profile81_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile81_node7
  · exact profile81_node11
  · exact profile81_node12

def profile81_node14_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile81_node14 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28,25] 2 profile81_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28,25] 2 profile81_node14_cert).mp (by decide +kernel))

def profile81_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node13 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28] 2 (by decide) (choices 3) [25] profile81_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [28] (choices 3) [25] profile81_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile81_node14

def profile81_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node0 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [] 2 (by decide) (choices 3) [14,26,28] profile81_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [] (choices 3) [14,26,28] profile81_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile81_node1
  · exact profile81_node6
  · exact profile81_node13

theorem profile81 : Upper (D (n:=5) [51,51,49,36,34]) (R (n:=5) [51,51,49,36,34]) [] 2 := profile81_node0

#print axioms profile81
end Delivery.FiveVertexPositive13
