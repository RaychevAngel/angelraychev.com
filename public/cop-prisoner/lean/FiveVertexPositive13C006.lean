import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile91_node4_cert : CutBound 5 := { lost := (rows 0 0 2 2 1), upper := (rows 15 27 29 25 26), lower := (rows 15 27 29 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 26 28 24 16) },{ target := 1, region := (rows 1 0 14 14 16), good := (rows 13 29 29 29 16) }] }

theorem profile91_node4 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,17] 2 profile91_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,17] 2 profile91_node4_cert).mp (by decide +kernel))

def profile91_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 27 29 26 25), lower := (rows 15 27 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) }] }

theorem profile91_node5 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,18] 2 profile91_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25,18] 2 profile91_node5_cert).mp (by decide +kernel))

def profile91_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node3 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25] 2 (by decide) (choices 2) [17,18] profile91_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,25] (choices 2) [17,18] profile91_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node4
  · exact profile91_node5

def profile91_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 27 30 25 25), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 25 28 8 16) }] }

theorem profile91_node6 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,26] 2 profile91_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25,26] 2 profile91_node6_cert).mp (by decide +kernel))

def profile91_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node2 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25] 2 (by decide) (choices 3) [25,26] profile91_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14,25] (choices 3) [25,26] profile91_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node3
  · exact profile91_node6

def profile91_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node1 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14] 2 (by decide) (choices 3) [25] profile91_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [14] (choices 3) [25] profile91_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node2

def profile91_node9_cert : CutBound 5 := { lost := (rows 0 16 2 0 0), upper := (rows 27 15 29 27 27), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 11 15 15 8 0) }] }

theorem profile91_node9 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,25] 2 profile91_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,25] 2 profile91_node9_cert).mp (by decide +kernel))

def profile91_node10_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 27 15 30 25 25), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 25 29 28 8 16) }] }

theorem profile91_node10 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,26] 2 profile91_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13,26] 2 profile91_node10_cert).mp (by decide +kernel))

def profile91_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node8 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13] 2 (by decide) (choices 3) [25,26] profile91_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,13] (choices 3) [25,26] profile91_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node9
  · exact profile91_node10

def profile91_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 27 15 29 29), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) }] }

theorem profile91_node12 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,11] 2 profile91_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,11] 2 profile91_node12_cert).mp (by decide +kernel))

def profile91_node14_cert : CutBound 5 := { lost := (rows 0 0 2 0 3), upper := (rows 27 27 29 11 28), lower := (rows 27 27 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 26 26 28 10 16) },{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) }] }

theorem profile91_node14 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,3] 2 profile91_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,3] 2 profile91_node14_cert).mp (by decide +kernel))

def profile91_node15_cert : CutBound 5 := { lost := (rows 0 0 2 2 1), upper := (rows 27 27 29 13 26), lower := (rows 27 27 29 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 26 26 28 28 16) },{ target := 1, region := (rows 1 0 7 15 16), good := (rows 29 29 29 13 16) }] }

theorem profile91_node15 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,5] 2 profile91_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,5] 2 profile91_node15_cert).mp (by decide +kernel))

def profile91_node16_cert : CutBound 5 := { lost := (rows 0 0 2 0 2), upper := (rows 27 27 29 14 25), lower := (rows 27 27 29 14 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) }] }

theorem profile91_node16 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,6] 2 profile91_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25,6] 2 profile91_node16_cert).mp (by decide +kernel))

def profile91_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node13 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25] 2 (by decide) (choices 2) [3,5,6] profile91_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,25] (choices 2) [3,5,6] profile91_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node14
  · exact profile91_node15
  · exact profile91_node16

def profile91_node18_cert : CutBound 5 := { lost := (rows 0 0 1 0 2), upper := (rows 27 27 30 13 25), lower := (rows 27 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 12 16) },{ target := 1, region := (rows 1 0 4 8 27), good := (rows 25 25 28 29 16) }] }

theorem profile91_node18 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26,5] 2 profile91_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26,5] 2 profile91_node18_cert).mp (by decide +kernel))

def profile91_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node17 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26] 2 (by decide) (choices 2) [5] profile91_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25,26] (choices 2) [5] profile91_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node18

def profile91_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node11 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25] 2 (by decide) (choices 3) [11,25,26] profile91_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,25] (choices 3) [11,25,26] profile91_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node12
  · exact profile91_node13
  · exact profile91_node17

def profile91_node20_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 27 30 15 25 25), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile91_node20 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,11] 2 profile91_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,11] 2 profile91_node20_cert).mp (by decide +kernel))

def profile91_node21_cert : CutBound 5 := { lost := (rows 0 1 2 0 0), upper := (rows 27 30 29 11 27), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) }] }

theorem profile91_node21 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,25] 2 profile91_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28,25] 2 profile91_node21_cert).mp (by decide +kernel))

def profile91_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node19 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28] 2 (by decide) (choices 3) [11,25] profile91_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26,28] (choices 3) [11,25] profile91_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node20
  · exact profile91_node21

def profile91_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node7 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26] 2 (by decide) (choices 3) [13,25,28] profile91_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [26] (choices 3) [13,25,28] profile91_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node8
  · exact profile91_node11
  · exact profile91_node19

def profile91_node25_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 29 27 15 25 26), lower := (rows 29 27 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 28 26 30 24 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 25 13 25 16) }] }

theorem profile91_node25 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,17] 2 profile91_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,17] 2 profile91_node25_cert).mp (by decide +kernel))

def profile91_node26_cert : CutBound 5 := { lost := (rows 2 0 0 1 2), upper := (rows 29 27 15 26 25), lower := (rows 29 27 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 28 26 14 26 16) },{ target := 1, region := (rows 5 0 4 8 23), good := (rows 29 25 29 24 16) }] }

theorem profile91_node26 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,18] 2 profile91_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11,18] 2 profile91_node26_cert).mp (by decide +kernel))

def profile91_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node24 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11] 2 (by decide) (choices 2) [17,18] profile91_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,11] (choices 2) [17,18] profile91_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node25
  · exact profile91_node26

def profile91_node27_cert : CutBound 5 := { lost := (rows 2 0 2 0 0), upper := (rows 29 27 29 11 27), lower := (rows 29 27 29 8 16), losses := [{ target := 1, region := (rows 7 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile91_node27 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,25] 2 profile91_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,25] 2 profile91_node27_cert).mp (by decide +kernel))

def profile91_node28_cert : CutBound 5 := { lost := (rows 2 0 1 0 0), upper := (rows 29 27 30 11 27), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) },{ target := 1, region := (rows 5 0 4 8 16), good := (rows 29 25 29 8 16) }] }

theorem profile91_node28 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,26] 2 profile91_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25,26] 2 profile91_node28_cert).mp (by decide +kernel))

def profile91_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node23 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25] 2 (by decide) (choices 3) [11,25,26] profile91_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28,25] (choices 3) [11,25,26] profile91_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node24
  · exact profile91_node27
  · exact profile91_node28

def profile91_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node22 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28] 2 (by decide) (choices 3) [25] profile91_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [28] (choices 3) [25] profile91_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node23

def profile91_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node0 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [] 2 (by decide) (choices 3) [14,26,28] profile91_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [] (choices 3) [14,26,28] profile91_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node1
  · exact profile91_node7
  · exact profile91_node22

theorem profile91 : Upper (D (n:=5) [51,50,49,36,35]) (R (n:=5) [51,50,49,36,35]) [] 2 := profile91_node0

def profile92_node4_cert : CutBound 5 := { lost := (rows 0 4 2 5 3), upper := (rows 15 27 29 26 28), lower := (rows 15 27 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 31), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 6 0 14 16), good := (rows 11 27 27 26 16) }] }

theorem profile92_node4 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,18] 2 profile92_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,18] 2 profile92_node4_cert).mp (by decide +kernel))

def profile92_node5_cert : CutBound 5 := { lost := (rows 0 4 2 3 5), upper := (rows 15 27 29 28 26), lower := (rows 15 27 29 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 6 14 16), good := (rows 13 29 29 28 16) },{ target := 2, region := (rows 1 7 0 8 31), good := (rows 27 27 27 26 16) }] }

theorem profile92_node5 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,20] 2 profile92_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25,20] 2 profile92_node5_cert).mp (by decide +kernel))

def profile92_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node3 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25] 2 (by decide) (choices 2) [18,20] profile92_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,25] (choices 2) [18,20] profile92_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node4
  · exact profile92_node5

def profile92_node7_cert : CutBound 5 := { lost := (rows 0 4 1 6 3), upper := (rows 15 27 30 25 28), lower := (rows 15 27 30 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 11 21), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 26 27 16) }] }

theorem profile92_node7 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,17] 2 profile92_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,17] 2 profile92_node7_cert).mp (by decide +kernel))

def profile92_node8_cert : CutBound 5 := { lost := (rows 0 4 1 3 6), upper := (rows 15 27 30 28 25), lower := (rows 15 27 30 28 16), losses := [{ target := 0, region := (rows 0 2 6 14 16), good := (rows 14 30 30 28 16) },{ target := 1, region := (rows 1 0 4 13 19), good := (rows 29 25 28 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 27 26 24 16) }] }

theorem profile92_node8 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,20] 2 profile92_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26,20] 2 profile92_node8_cert).mp (by decide +kernel))

def profile92_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node6 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26] 2 (by decide) (choices 2) [17,20] profile92_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25,26] (choices 2) [17,20] profile92_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node7
  · exact profile92_node8

def profile92_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node2 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25] 2 (by decide) (choices 3) [25,26] profile92_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,25] (choices 3) [25,26] profile92_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node3
  · exact profile92_node6

def profile92_node11_cert : CutBound 5 := { lost := (rows 0 1 2 6 5), upper := (rows 15 30 29 25 26), lower := (rows 15 30 29 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 31), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 28 29 29 16) },{ target := 2, region := (rows 1 2 0 13 19), good := (rows 27 26 25 25 16) }] }

theorem profile92_node11 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,17] 2 profile92_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,17] 2 profile92_node11_cert).mp (by decide +kernel))

def profile92_node12_cert : CutBound 5 := { lost := (rows 0 1 2 5 6), upper := (rows 15 30 29 26 25), lower := (rows 15 30 29 26 16), losses := [{ target := 0, region := (rows 0 6 4 14 16), good := (rows 14 30 30 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 29 24 16) },{ target := 2, region := (rows 1 2 0 11 21), good := (rows 27 26 25 26 16) }] }

theorem profile92_node12 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,18] 2 profile92_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25,18] 2 profile92_node12_cert).mp (by decide +kernel))

def profile92_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node10 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25] 2 (by decide) (choices 2) [17,18] profile92_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,25] (choices 2) [17,18] profile92_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node11
  · exact profile92_node12

def profile92_node13_cert : CutBound 5 := { lost := (rows 0 1 1 6 6), upper := (rows 15 30 30 25 25), lower := (rows 15 30 30 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 26 8 16) }] }

theorem profile92_node13 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,26] 2 profile92_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28,26] 2 profile92_node13_cert).mp (by decide +kernel))

def profile92_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node9 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28] 2 (by decide) (choices 3) [25,26] profile92_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14,28] (choices 3) [25,26] profile92_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node10
  · exact profile92_node13

def profile92_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node1 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14] 2 (by decide) (choices 3) [25,28] profile92_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [14] (choices 3) [25,28] profile92_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node2
  · exact profile92_node9

def profile92_node17_cert : CutBound 5 := { lost := (rows 4 0 2 5 3), upper := (rows 27 15 29 26 28), lower := (rows 27 15 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 22), good := (rows 26 30 28 26 16) },{ target := 1, region := (rows 1 0 7 8 31), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 9 2 0 9 16), good := (rows 27 11 25 27 16) }] }

theorem profile92_node17 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,18] 2 profile92_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,18] 2 profile92_node17_cert).mp (by decide +kernel))

def profile92_node18_cert : CutBound 5 := { lost := (rows 4 0 2 3 5), upper := (rows 27 15 29 28 26), lower := (rows 27 15 29 28 16), losses := [{ target := 0, region := (rows 0 2 4 14 19), good := (rows 26 30 28 28 16) },{ target := 1, region := (rows 1 0 5 13 16), good := (rows 29 13 29 28 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 24 16) }] }

theorem profile92_node18 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,20] 2 profile92_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25,20] 2 profile92_node18_cert).mp (by decide +kernel))

def profile92_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node16 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25] 2 (by decide) (choices 2) [18,20] profile92_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,25] (choices 2) [18,20] profile92_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node17
  · exact profile92_node18

def profile92_node20_cert : CutBound 5 := { lost := (rows 4 0 1 6 3), upper := (rows 27 15 30 25 28), lower := (rows 27 15 30 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 11 22), good := (rows 25 29 28 25 16) },{ target := 2, region := (rows 5 2 0 13 16), good := (rows 27 11 27 25 16) }] }

theorem profile92_node20 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,17] 2 profile92_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,17] 2 profile92_node20_cert).mp (by decide +kernel))

def profile92_node21_cert : CutBound 5 := { lost := (rows 4 0 1 3 6), upper := (rows 27 15 30 28 25), lower := (rows 27 15 30 28 16), losses := [{ target := 0, region := (rows 0 2 5 13 16), good := (rows 30 14 30 28 16) },{ target := 1, region := (rows 1 0 4 14 19), good := (rows 25 29 28 28 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 27 27 27 25 16) }] }

theorem profile92_node21 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,20] 2 profile92_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26,20] 2 profile92_node21_cert).mp (by decide +kernel))

def profile92_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node19 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26] 2 (by decide) (choices 2) [17,20] profile92_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13,26] (choices 2) [17,20] profile92_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node20
  · exact profile92_node21

def profile92_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node15 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13] 2 (by decide) (choices 3) [25,26] profile92_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,13] (choices 3) [25,26] profile92_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node16
  · exact profile92_node19

def profile92_node23_cert : CutBound 5 := { lost := (rows 4 4 0 3 3), upper := (rows 27 27 15 28 28), lower := (rows 27 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 26 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) }] }

theorem profile92_node23 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,11] 2 profile92_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,11] 2 profile92_node23_cert).mp (by decide +kernel))

def profile92_node25_cert : CutBound 5 := { lost := (rows 4 4 2 0 3), upper := (rows 27 27 29 14 28), lower := (rows 27 27 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 8 28), good := (rows 26 26 28 30 16) },{ target := 1, region := (rows 1 0 7 8 31), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 11 16) }] }

theorem profile92_node25 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25,6] 2 profile92_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25,6] 2 profile92_node25_cert).mp (by decide +kernel))

def profile92_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node24 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25] 2 (by decide) (choices 2) [6] profile92_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,25] (choices 2) [6] profile92_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node25

def profile92_node27_cert : CutBound 5 := { lost := (rows 4 4 1 0 3), upper := (rows 27 27 30 13 28), lower := (rows 27 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 8 28), good := (rows 25 25 28 29 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 11 16) }] }

theorem profile92_node27 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26,5] 2 profile92_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26,5] 2 profile92_node27_cert).mp (by decide +kernel))

def profile92_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node26 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26] 2 (by decide) (choices 2) [5] profile92_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25,26] (choices 2) [5] profile92_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node27

def profile92_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node22 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25] 2 (by decide) (choices 3) [11,25,26] profile92_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,25] (choices 3) [11,25,26] profile92_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node23
  · exact profile92_node24
  · exact profile92_node26

def profile92_node30_cert : CutBound 5 := { lost := (rows 4 1 0 6 3), upper := (rows 27 30 15 25 28), lower := (rows 27 30 15 25 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 26 30 30 24 16) },{ target := 1, region := (rows 1 0 4 13 22), good := (rows 25 28 29 25 16) },{ target := 2, region := (rows 3 2 0 11 16), good := (rows 27 27 11 25 16) }] }

theorem profile92_node30 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,17] 2 profile92_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,17] 2 profile92_node30_cert).mp (by decide +kernel))

def profile92_node31_cert : CutBound 5 := { lost := (rows 4 1 0 3 6), upper := (rows 27 30 15 28 25), lower := (rows 27 30 15 28 16), losses := [{ target := 0, region := (rows 0 10 4 10 16), good := (rows 26 30 14 30 16) },{ target := 1, region := (rows 1 0 4 14 21), good := (rows 25 28 29 28 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 27 27 27 25 16) }] }

theorem profile92_node31 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,20] 2 profile92_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11,20] 2 profile92_node31_cert).mp (by decide +kernel))

def profile92_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node29 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11] 2 (by decide) (choices 2) [17,20] profile92_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,11] (choices 2) [17,20] profile92_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node30
  · exact profile92_node31

def profile92_node33_cert : CutBound 5 := { lost := (rows 4 1 2 4 3), upper := (rows 27 30 29 11 28), lower := (rows 27 30 29 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 26 30 30 26 16) },{ target := 1, region := (rows 1 0 13 8 31), good := (rows 29 28 29 29 16) },{ target := 2, region := (rows 3 2 0 11 16), good := (rows 27 27 25 11 16) }] }

theorem profile92_node33 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,3] 2 profile92_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,3] 2 profile92_node33_cert).mp (by decide +kernel))

def profile92_node34_cert : CutBound 5 := { lost := (rows 4 1 2 2 5), upper := (rows 27 30 29 13 26), lower := (rows 27 30 29 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 31), good := (rows 26 30 30 30 16) },{ target := 1, region := (rows 1 0 5 13 16), good := (rows 29 28 29 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 27 27 25 25 16) }] }

theorem profile92_node34 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,5] 2 profile92_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,5] 2 profile92_node34_cert).mp (by decide +kernel))

def profile92_node35_cert : CutBound 5 := { lost := (rows 4 1 2 1 6), upper := (rows 27 30 29 14 25), lower := (rows 27 30 29 14 16), losses := [{ target := 0, region := (rows 0 6 4 14 16), good := (rows 26 30 30 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 29 28 16) },{ target := 2, region := (rows 11 2 0 8 31), good := (rows 27 27 25 27 16) }] }

theorem profile92_node35 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,6] 2 profile92_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25,6] 2 profile92_node35_cert).mp (by decide +kernel))

def profile92_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node32 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25] 2 (by decide) (choices 2) [3,5,6] profile92_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,25] (choices 2) [3,5,6] profile92_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node33
  · exact profile92_node34
  · exact profile92_node35

def profile92_node37_cert : CutBound 5 := { lost := (rows 4 1 1 0 6), upper := (rows 27 30 30 13 25), lower := (rows 27 30 30 13 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 14 16) },{ target := 1, region := (rows 1 0 4 8 25), good := (rows 25 28 28 29 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 27 27 27 25 16) }] }

theorem profile92_node37 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26,5] 2 profile92_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26,5] 2 profile92_node37_cert).mp (by decide +kernel))

def profile92_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node36 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26] 2 (by decide) (choices 2) [5] profile92_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28,26] (choices 2) [5] profile92_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node37

def profile92_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node28 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28] 2 (by decide) (choices 3) [11,25,26] profile92_node28_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26,28] (choices 3) [11,25,26] profile92_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node29
  · exact profile92_node32
  · exact profile92_node36

def profile92_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node14 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26] 2 (by decide) (choices 3) [13,25,28] profile92_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [26] (choices 3) [13,25,28] profile92_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node15
  · exact profile92_node22
  · exact profile92_node28

def profile92_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile92_node0 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [] 2 (by decide) (choices 3) [14,26] profile92_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [] (choices 3) [14,26] profile92_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node1
  · exact profile92_node14

theorem profile92 : Upper (D (n:=5) [50,50,50,36,35]) (R (n:=5) [50,50,50,36,35]) [] 2 := profile92_node0

def profile93_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 27 27 29 26 28), lower := (rows 27 27 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 20), good := (rows 26 26 28 26 16) }] }

theorem profile93_node4 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,18] 2 profile93_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,18] 2 profile93_node4_cert).mp (by decide +kernel))

def profile93_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 27 27 29 28 26), lower := (rows 27 27 29 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 19), good := (rows 26 26 28 28 16) }] }

theorem profile93_node5 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,20] 2 profile93_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25,20] 2 profile93_node5_cert).mp (by decide +kernel))

def profile93_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node3 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25] 2 (by decide) (choices 2) [18,20] profile93_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,25] (choices 2) [18,20] profile93_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node4
  · exact profile93_node5

def profile93_node7_cert : CutBound 5 := { lost := (rows 0 0 1 0 1), upper := (rows 27 27 30 25 28), lower := (rows 27 27 30 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 30 30 28 16) }] }

theorem profile93_node7 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,17] 2 profile93_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,17] 2 profile93_node7_cert).mp (by decide +kernel))

def profile93_node8_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 27 27 30 28 25), lower := (rows 27 27 30 28 16), losses := [{ target := 0, region := (rows 0 2 7 15 16), good := (rows 30 30 30 28 16) }] }

theorem profile93_node8 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,20] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,20] 2 profile93_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26,20] 2 profile93_node8_cert).mp (by decide +kernel))

def profile93_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node6 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26] 2 (by decide) (choices 2) [17,20] profile93_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25,26] (choices 2) [17,20] profile93_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node7
  · exact profile93_node8

def profile93_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node2 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25] 2 (by decide) (choices 3) [25,26] profile93_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,25] (choices 3) [25,26] profile93_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node3
  · exact profile93_node6

def profile93_node10_cert : CutBound 5 := { lost := (rows 0 1 2 0 0), upper := (rows 27 30 29 27 27), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) }] }

theorem profile93_node10 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,25] 2 profile93_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,25] 2 profile93_node10_cert).mp (by decide +kernel))

def profile93_node11_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 27 30 30 25 25), lower := (rows 27 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile93_node11 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,26] 2 profile93_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28,26] 2 profile93_node11_cert).mp (by decide +kernel))

def profile93_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node9 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28] 2 (by decide) (choices 3) [25,26] profile93_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26,28] (choices 3) [25,26] profile93_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node10
  · exact profile93_node11

def profile93_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node1 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26] 2 (by decide) (choices 3) [25,28] profile93_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [26] (choices 3) [25,28] profile93_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node2
  · exact profile93_node9

def profile93_node14_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 29 27 29 26 26), lower := (rows 29 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 26 28 8 16) }] }

theorem profile93_node14 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,25] 2 profile93_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,25] 2 profile93_node14_cert).mp (by decide +kernel))

def profile93_node15_cert : CutBound 5 := { lost := (rows 2 0 1 0 0), upper := (rows 29 27 30 27 27), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) },{ target := 1, region := (rows 5 0 4 8 16), good := (rows 29 25 29 8 16) }] }

theorem profile93_node15 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,26] 2 profile93_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25,26] 2 profile93_node15_cert).mp (by decide +kernel))

def profile93_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node13 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25] 2 (by decide) (choices 3) [25,26] profile93_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28,25] (choices 3) [25,26] profile93_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node14
  · exact profile93_node15

def profile93_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node12 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28] 2 (by decide) (choices 3) [25] profile93_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [28] (choices 3) [25] profile93_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node13

def profile93_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node0 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [] 2 (by decide) (choices 3) [26,28] profile93_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [] (choices 3) [26,28] profile93_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile93_node1
  · exact profile93_node12

theorem profile93 : Upper (D (n:=5) [50,50,49,36,36]) (R (n:=5) [50,50,49,36,36]) [] 2 := profile93_node0

#print axioms profile93
end Delivery.FiveVertexPositive13
