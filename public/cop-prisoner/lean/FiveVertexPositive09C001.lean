import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive09
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile4_node2_cert : CutBound 5 := { lost := (rows 16 16 0 4 0), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 7 7 7 8 0) }] }

theorem profile4_node2 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 3 profile4_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,5] 3 profile4_node2_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 5 := { lost := (rows 0 4 2 5 0), upper := (rows 7 11 21 26 20), lower := (rows 7 11 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 31), good := (rows 21 29 21 28 16) },{ target := 2, region := (rows 1 7 0 12 16), good := (rows 11 11 27 26 16) }] }

theorem profile4_node5 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 3 profile4_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,18] 3 profile4_node5_cert).mp (by decide +kernel))

def profile4_node6_cert : CutBound 5 := { lost := (rows 16 16 0 3 0), upper := (rows 7 11 21 28 18), lower := (rows 7 11 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 9 29 28 16) },{ target := 4, region := (rows 9 10 4 8 0), good := (rows 7 11 5 15 0) }] }

theorem profile4_node6 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 3 profile4_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17,20] 3 profile4_node6_cert).mp (by decide +kernel))

def profile4_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node4 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] 3 (by decide) (choices 2) [18,20] profile4_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,17] (choices 2) [18,20] profile4_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node5
  · exact profile4_node6

def profile4_node8_cert : CutBound 5 := { lost := (rows 0 4 1 2 0), upper := (rows 7 11 22 25 20), lower := (rows 7 11 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 22 30 22 28 16) },{ target := 1, region := (rows 1 0 4 11 21), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 11 18 27 16) }] }

theorem profile4_node8 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,17] 3 profile4_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,17] 3 profile4_node8_cert).mp (by decide +kernel))

def profile4_node9_cert : CutBound 5 := { lost := (rows 16 16 0 3 0), upper := (rows 7 11 22 28 17), lower := (rows 7 11 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 10 30 28 16) },{ target := 1, region := (rows 1 0 4 13 19), good := (rows 29 25 28 28 16) },{ target := 4, region := (rows 13 10 4 8 0), good := (rows 7 11 7 15 0) }] }

theorem profile4_node9 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,20] 3 profile4_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18,20] 3 profile4_node9_cert).mp (by decide +kernel))

def profile4_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node7 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] 3 (by decide) (choices 2) [17,20] profile4_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9,18] (choices 2) [17,20] profile4_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node8
  · exact profile4_node9

def profile4_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] 3 (by decide) (choices 2) [17,18] profile4_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,9] (choices 2) [17,18] profile4_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node4
  · exact profile4_node7

def profile4_node12_cert : CutBound 5 := { lost := (rows 0 0 2 6 0), upper := (rows 7 14 21 25 18), lower := (rows 7 14 21 25 16), losses := [{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 12 29 29 16) },{ target := 2, region := (rows 1 2 0 13 19), good := (rows 27 26 25 25 16) }] }

theorem profile4_node12 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,17] 3 profile4_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,17] 3 profile4_node12_cert).mp (by decide +kernel))

def profile4_node13_cert : CutBound 5 := { lost := (rows 0 1 2 1 0), upper := (rows 7 14 21 26 17), lower := (rows 7 14 21 26 16), losses := [{ target := 0, region := (rows 0 7 4 12 16), good := (rows 14 14 30 26 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 21 28 21 24 16) }] }

theorem profile4_node13 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,18] 3 profile4_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17,18] 3 profile4_node13_cert).mp (by decide +kernel))

def profile4_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node11 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17] 3 (by decide) (choices 2) [17,18] profile4_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,17] (choices 2) [17,18] profile4_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node12
  · exact profile4_node13

def profile4_node14_cert : CutBound 5 := { lost := (rows 16 0 0 6 0), upper := (rows 7 14 22 25 17), lower := (rows 7 14 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 12 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 18 8 16) },{ target := 4, region := (rows 7 2 4 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile4_node14 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,18] 3 profile4_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12,18] 3 profile4_node14_cert).mp (by decide +kernel))

def profile4_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node10 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] 3 (by decide) (choices 2) [17,18] profile4_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,12] (choices 2) [17,18] profile4_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node11
  · exact profile4_node14

def profile4_node16_cert : CutBound 5 := { lost := (rows 16 0 16 3 0), upper := (rows 7 19 7 28 28), lower := (rows 7 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 7 7 8 0) }] }

theorem profile4_node16 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 3 profile4_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,3] 3 profile4_node16_cert).mp (by decide +kernel))

def profile4_node18_cert : CutBound 5 := { lost := (rows 16 0 16 5 0), upper := (rows 7 19 13 26 20), lower := (rows 7 19 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 26 16) },{ target := 4, region := (rows 9 2 12 8 0), good := (rows 7 3 13 15 0) }] }

theorem profile4_node18 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 3 profile4_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,18] 3 profile4_node18_cert).mp (by decide +kernel))

def profile4_node19_cert : CutBound 5 := { lost := (rows 0 0 2 3 0), upper := (rows 7 19 13 28 18), lower := (rows 7 19 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 7 10 16), good := (rows 13 29 13 28 16) }] }

theorem profile4_node19 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 3 profile4_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9,20] 3 profile4_node19_cert).mp (by decide +kernel))

def profile4_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node17 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] 3 (by decide) (choices 2) [18,20] profile4_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,9] (choices 2) [18,20] profile4_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node18
  · exact profile4_node19

def profile4_node21_cert : CutBound 5 := { lost := (rows 0 4 0 6 0), upper := (rows 7 19 14 25 20), lower := (rows 7 19 14 25 16), losses := [{ target := 1, region := (rows 1 0 4 11 21), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 10 27 16) }] }

theorem profile4_node21 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,17] 3 profile4_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,17] 3 profile4_node21_cert).mp (by decide +kernel))

def profile4_node22_cert : CutBound 5 := { lost := (rows 0 0 1 3 0), upper := (rows 7 19 14 28 17), lower := (rows 7 19 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 10 16), good := (rows 14 30 14 28 16) },{ target := 1, region := (rows 1 0 4 13 19), good := (rows 29 25 28 28 16) }] }

theorem profile4_node22 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,20] 3 profile4_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10,20] 3 profile4_node22_cert).mp (by decide +kernel))

def profile4_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node20 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] 3 (by decide) (choices 2) [17,20] profile4_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,10] (choices 2) [17,20] profile4_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node21
  · exact profile4_node22

def profile4_node23_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 7 19 21 14 30), lower := (rows 7 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 21 21 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 3 19 19 8 16) }] }

theorem profile4_node23 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 3 profile4_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,17] 3 profile4_node23_cert).mp (by decide +kernel))

def profile4_node24_cert : CutBound 5 := { lost := (rows 16 0 1 18 0), upper := (rows 7 19 22 13 29), lower := (rows 7 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile4_node24 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 3 profile4_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,18] 3 profile4_node24_cert).mp (by decide +kernel))

def profile4_node26_cert : CutBound 5 := { lost := (rows 0 0 3 4 0), upper := (rows 7 19 28 11 20), lower := (rows 7 19 28 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 29), good := (rows 22 18 28 30 16) },{ target := 1, region := (rows 1 0 12 8 29), good := (rows 21 17 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) }] }

theorem profile4_node26 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 3 profile4_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,3] 3 profile4_node26_cert).mp (by decide +kernel))

def profile4_node27_cert : CutBound 5 := { lost := (rows 0 0 3 2 0), upper := (rows 7 19 28 13 18), lower := (rows 7 19 28 13 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 22 18 28 28 16) },{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) }] }

theorem profile4_node27 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 3 profile4_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,5] 3 profile4_node27_cert).mp (by decide +kernel))

def profile4_node28_cert : CutBound 5 := { lost := (rows 0 0 3 1 0), upper := (rows 7 19 28 14 17), lower := (rows 7 19 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) },{ target := 1, region := (rows 1 0 12 8 19), good := (rows 21 17 28 28 16) }] }

theorem profile4_node28 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 3 profile4_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24,6] 3 profile4_node28_cert).mp (by decide +kernel))

def profile4_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node25 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] 3 (by decide) (choices 2) [3,5,6] profile4_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17,24] (choices 2) [3,5,6] profile4_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node26
  · exact profile4_node27
  · exact profile4_node28

def profile4_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node15 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile4_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,17] (choices 2) [3,9,10,17,18,24] profile4_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node16
  · exact profile4_node17
  · exact profile4_node20
  · exact profile4_node23
  · exact profile4_node24
  · exact profile4_node25

def profile4_node30_cert : CutBound 5 := { lost := (rows 16 0 16 6 0), upper := (rows 7 22 7 25 25), lower := (rows 7 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 7 7 8 0) }] }

theorem profile4_node30 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,3] 3 profile4_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,3] 3 profile4_node30_cert).mp (by decide +kernel))

def profile4_node32_cert : CutBound 5 := { lost := (rows 0 1 2 4 0), upper := (rows 7 22 13 25 18), lower := (rows 7 22 13 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 31), good := (rows 22 22 30 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 20 13 29 16) },{ target := 2, region := (rows 1 2 0 13 19), good := (rows 27 26 25 25 16) }] }

theorem profile4_node32 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,17] 3 profile4_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,17] 3 profile4_node32_cert).mp (by decide +kernel))

def profile4_node33_cert : CutBound 5 := { lost := (rows 16 0 16 5 0), upper := (rows 7 22 13 26 17), lower := (rows 7 22 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 12 26 16) },{ target := 2, region := (rows 1 2 0 11 21), good := (rows 27 26 25 26 16) },{ target := 4, region := (rows 11 2 12 8 0), good := (rows 7 7 13 15 0) }] }

theorem profile4_node33 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,18] 3 profile4_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9,18] 3 profile4_node33_cert).mp (by decide +kernel))

def profile4_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node31 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9] 3 (by decide) (choices 2) [17,18] profile4_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,9] (choices 2) [17,18] profile4_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node32
  · exact profile4_node33

def profile4_node34_cert : CutBound 5 := { lost := (rows 16 0 0 6 0), upper := (rows 7 22 14 25 17), lower := (rows 7 22 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 20 12 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) },{ target := 4, region := (rows 7 2 4 8 0), good := (rows 7 7 15 8 0) }] }

theorem profile4_node34 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,10] 3 profile4_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,10] 3 profile4_node34_cert).mp (by decide +kernel))

def profile4_node35_cert : CutBound 5 := { lost := (rows 16 1 0 20 0), upper := (rows 7 22 21 11 27), lower := (rows 7 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 6 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile4_node35 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,17] 3 profile4_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,17] 3 profile4_node35_cert).mp (by decide +kernel))

def profile4_node36_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 7 22 22 9 25), lower := (rows 7 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 6 22 22 8 22) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 20 20 8 16) }] }

theorem profile4_node36 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,18] 3 profile4_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,18] 3 profile4_node36_cert).mp (by decide +kernel))

def profile4_node37_cert : CutBound 5 := { lost := (rows 16 1 0 20 0), upper := (rows 7 22 28 11 19), lower := (rows 7 22 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 6 22 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 24 8 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile4_node37 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,24] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,24] 3 profile4_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20,24] 3 profile4_node37_cert).mp (by decide +kernel))

def profile4_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node29 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile4_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,20] (choices 2) [3,9,10,17,18,24] profile4_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node30
  · exact profile4_node31
  · exact profile4_node34
  · exact profile4_node35
  · exact profile4_node36
  · exact profile4_node37

def profile4_node39_cert : CutBound 5 := { lost := (rows 16 0 16 2 0), upper := (rows 7 26 7 29 21), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile4_node39 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 3 profile4_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,3] 3 profile4_node39_cert).mp (by decide +kernel))

def profile4_node41_cert : CutBound 5 := { lost := (rows 0 5 2 4 0), upper := (rows 7 26 21 11 20), lower := (rows 7 26 21 11 16), losses := [{ target := 0, region := (rows 0 10 4 8 21), good := (rows 22 26 20 26 16) },{ target := 1, region := (rows 1 0 13 8 31), good := (rows 21 28 21 29 16) },{ target := 2, region := (rows 1 6 0 13 16), good := (rows 11 26 27 11 16) }] }

theorem profile4_node41 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 3 profile4_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,3] 3 profile4_node41_cert).mp (by decide +kernel))

def profile4_node42_cert : CutBound 5 := { lost := (rows 0 5 0 2 0), upper := (rows 7 26 21 13 18), lower := (rows 7 26 21 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 27), good := (rows 22 26 20 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 24 29 13 16) },{ target := 2, region := (rows 1 10 0 8 27), good := (rows 19 26 17 27 16) }] }

theorem profile4_node42 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 3 profile4_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,5] 3 profile4_node42_cert).mp (by decide +kernel))

def profile4_node43_cert : CutBound 5 := { lost := (rows 0 1 2 1 0), upper := (rows 7 26 21 14 17), lower := (rows 7 26 21 14 16), losses := [{ target := 0, region := (rows 0 6 4 13 16), good := (rows 14 26 30 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 21 24 21 28 16) }] }

theorem profile4_node43 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 3 profile4_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17,6] 3 profile4_node43_cert).mp (by decide +kernel))

def profile4_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node40 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] 3 (by decide) (choices 2) [3,5,6] profile4_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,17] (choices 2) [3,5,6] profile4_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node41
  · exact profile4_node42
  · exact profile4_node43

def profile4_node44_cert : CutBound 5 := { lost := (rows 16 0 1 18 0), upper := (rows 7 26 22 13 21), lower := (rows 7 26 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 20 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 10 15 8 0) }] }

theorem profile4_node44 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 3 profile4_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24,18] 3 profile4_node44_cert).mp (by decide +kernel))

def profile4_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node38 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] 3 (by decide) (choices 2) [3,17,18] profile4_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6,24] (choices 2) [3,17,18] profile4_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node39
  · exact profile4_node40
  · exact profile4_node44

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile4_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [6] (choices 2) [5,9,12,17,20,24] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node10
  · exact profile4_node15
  · exact profile4_node29
  · exact profile4_node38

def profile4_node48_cert : CutBound 5 := { lost := (rows 4 0 2 1 0), upper := (rows 11 7 21 26 20), lower := (rows 11 7 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 22), good := (rows 26 30 28 26 16) },{ target := 1, region := (rows 1 0 7 8 31), good := (rows 29 21 21 28 16) },{ target := 2, region := (rows 9 2 0 8 16), good := (rows 11 3 17 27 16) }] }

theorem profile4_node48 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,18] 3 profile4_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,18] 3 profile4_node48_cert).mp (by decide +kernel))

def profile4_node49_cert : CutBound 5 := { lost := (rows 16 16 0 3 0), upper := (rows 11 7 21 28 18), lower := (rows 11 7 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 14 19), good := (rows 26 30 28 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 9 13 29 28 16) },{ target := 4, region := (rows 9 14 4 8 0), good := (rows 11 7 7 15 0) }] }

theorem profile4_node49 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,20] 3 profile4_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17,20] 3 profile4_node49_cert).mp (by decide +kernel))

def profile4_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node47 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] 3 (by decide) (choices 2) [18,20] profile4_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,17] (choices 2) [18,20] profile4_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node48
  · exact profile4_node49

def profile4_node51_cert : CutBound 5 := { lost := (rows 4 0 1 6 0), upper := (rows 11 7 22 25 20), lower := (rows 11 7 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 11 22), good := (rows 25 29 28 25 16) },{ target := 2, region := (rows 7 2 0 12 16), good := (rows 11 11 27 25 16) }] }

theorem profile4_node51 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 3 profile4_node51_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,17] 3 profile4_node51_cert).mp (by decide +kernel))

def profile4_node52_cert : CutBound 5 := { lost := (rows 16 16 0 3 0), upper := (rows 11 7 22 28 17), lower := (rows 11 7 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 10 14 30 28 16) },{ target := 1, region := (rows 1 0 4 14 19), good := (rows 25 29 28 28 16) },{ target := 4, region := (rows 9 10 4 8 0), good := (rows 11 7 6 15 0) }] }

theorem profile4_node52 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 3 profile4_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18,20] 3 profile4_node52_cert).mp (by decide +kernel))

def profile4_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node50 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] 3 (by decide) (choices 2) [17,20] profile4_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5,18] (choices 2) [17,20] profile4_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node51
  · exact profile4_node52

def profile4_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node46 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] 3 (by decide) (choices 2) [17,18] profile4_node46_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,5] (choices 2) [17,18] profile4_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node47
  · exact profile4_node50

def profile4_node54_cert : CutBound 5 := { lost := (rows 0 0 16 3 0), upper := (rows 11 19 7 28 20), lower := (rows 11 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 10 18 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 9 17 29 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile4_node54 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 3 profile4_node54_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,3] 3 profile4_node54_cert).mp (by decide +kernel))

def profile4_node56_cert : CutBound 5 := { lost := (rows 4 4 2 0 0), upper := (rows 11 19 21 14 20), lower := (rows 11 19 21 14 16), losses := [{ target := 1, region := (rows 1 0 7 8 31), good := (rows 29 21 21 28 16) },{ target := 2, region := (rows 9 6 0 8 16), good := (rows 11 19 19 11 16) }] }

theorem profile4_node56 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17,6] 3 profile4_node56_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17,6] 3 profile4_node56_cert).mp (by decide +kernel))

def profile4_node55_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node55 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] 3 (by decide) (choices 2) [6] profile4_node55_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,17] (choices 2) [6] profile4_node55_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node56

def profile4_node57_cert : CutBound 5 := { lost := (rows 16 0 1 16 0), upper := (rows 11 19 22 13 21), lower := (rows 11 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 4, region := (rows 5 2 4 12 0), good := (rows 11 3 15 8 0) }] }

theorem profile4_node57 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 3 profile4_node57_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17,18] 3 profile4_node57_cert).mp (by decide +kernel))

def profile4_node53_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node53 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] 3 (by decide) (choices 2) [3,17,18] profile4_node53_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,17] (choices 2) [3,17,18] profile4_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node54
  · exact profile4_node55
  · exact profile4_node57

def profile4_node60_cert : CutBound 5 := { lost := (rows 4 1 0 6 0), upper := (rows 11 22 7 25 20), lower := (rows 11 22 7 25 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 26 22 22 24 16) },{ target := 1, region := (rows 1 0 4 13 22), good := (rows 25 28 29 25 16) },{ target := 2, region := (rows 7 2 0 10 16), good := (rows 11 27 11 25 16) }] }

theorem profile4_node60 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,17] 3 profile4_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,17] 3 profile4_node60_cert).mp (by decide +kernel))

def profile4_node61_cert : CutBound 5 := { lost := (rows 0 1 0 3 0), upper := (rows 11 22 7 28 17), lower := (rows 11 22 7 28 16), losses := [{ target := 0, region := (rows 0 10 4 10 16), good := (rows 10 30 14 30 16) },{ target := 1, region := (rows 1 0 4 14 21), good := (rows 25 28 29 28 16) }] }

theorem profile4_node61 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,20] 3 profile4_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3,20] 3 profile4_node61_cert).mp (by decide +kernel))

def profile4_node59_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node59 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] 3 (by decide) (choices 2) [17,20] profile4_node59_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,3] (choices 2) [17,20] profile4_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node60
  · exact profile4_node61

def profile4_node62_cert : CutBound 5 := { lost := (rows 16 1 0 16 0), upper := (rows 11 22 21 15 23), lower := (rows 11 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 10 22 22 8 16) },{ target := 4, region := (rows 3 2 4 10 0), good := (rows 11 15 5 8 0) }] }

theorem profile4_node62 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 3 profile4_node62_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,17] 3 profile4_node62_cert).mp (by decide +kernel))

def profile4_node63_cert : CutBound 5 := { lost := (rows 16 1 1 16 0), upper := (rows 11 22 22 13 21), lower := (rows 11 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) },{ target := 4, region := (rows 7 2 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile4_node63 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 3 profile4_node63_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20,18] 3 profile4_node63_cert).mp (by decide +kernel))

def profile4_node58_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node58 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] 3 (by decide) (choices 2) [3,17,18] profile4_node58_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10,20] (choices 2) [3,17,18] profile4_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node59
  · exact profile4_node62
  · exact profile4_node63

def profile4_node45_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node45 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] 3 (by decide) (choices 2) [5,17,20] profile4_node45_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [10] (choices 2) [5,17,20] profile4_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node46
  · exact profile4_node53
  · exact profile4_node58

def profile4_node66_cert : CutBound 5 := { lost := (rows 0 16 16 3 0), upper := (rows 19 7 7 28 28), lower := (rows 19 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 7 7 7 8 0) }] }

theorem profile4_node66 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 3 profile4_node66_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,3] 3 profile4_node66_cert).mp (by decide +kernel))

def profile4_node68_cert : CutBound 5 := { lost := (rows 4 0 0 5 0), upper := (rows 19 7 13 26 20), lower := (rows 19 7 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 22), good := (rows 26 30 28 26 16) },{ target := 2, region := (rows 9 2 0 9 16), good := (rows 27 11 9 27 16) }] }

theorem profile4_node68 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,18] 3 profile4_node68_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,18] 3 profile4_node68_cert).mp (by decide +kernel))

def profile4_node69_cert : CutBound 5 := { lost := (rows 0 0 2 3 0), upper := (rows 19 7 13 28 18), lower := (rows 19 7 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 14 19), good := (rows 26 30 28 28 16) },{ target := 1, region := (rows 1 0 7 9 16), good := (rows 29 13 13 28 16) }] }

theorem profile4_node69 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,20] 3 profile4_node69_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9,20] 3 profile4_node69_cert).mp (by decide +kernel))

def profile4_node67_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node67 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] 3 (by decide) (choices 2) [18,20] profile4_node67_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,9] (choices 2) [18,20] profile4_node67_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node68
  · exact profile4_node69

def profile4_node71_cert : CutBound 5 := { lost := (rows 0 16 16 6 0), upper := (rows 19 7 14 25 20), lower := (rows 19 7 14 25 16), losses := [{ target := 1, region := (rows 1 0 4 11 22), good := (rows 25 29 28 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 25 16) },{ target := 4, region := (rows 1 10 12 8 0), good := (rows 3 7 14 15 0) }] }

theorem profile4_node71 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 3 profile4_node71_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,17] 3 profile4_node71_cert).mp (by decide +kernel))

def profile4_node72_cert : CutBound 5 := { lost := (rows 0 0 1 3 0), upper := (rows 19 7 14 28 17), lower := (rows 19 7 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 14 19), good := (rows 25 29 28 28 16) }] }

theorem profile4_node72 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 3 profile4_node72_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10,20] 3 profile4_node72_cert).mp (by decide +kernel))

def profile4_node70_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node70 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] 3 (by decide) (choices 2) [17,20] profile4_node70_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,10] (choices 2) [17,20] profile4_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node71
  · exact profile4_node72

def profile4_node73_cert : CutBound 5 := { lost := (rows 0 16 2 17 0), upper := (rows 19 7 21 14 30), lower := (rows 19 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 5 21 8 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile4_node73 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 3 profile4_node73_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,17] 3 profile4_node73_cert).mp (by decide +kernel))

def profile4_node74_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 19 7 22 13 29), lower := (rows 19 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 6 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 19 3 19 8 16) }] }

theorem profile4_node74 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 3 profile4_node74_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,18] 3 profile4_node74_cert).mp (by decide +kernel))

def profile4_node76_cert : CutBound 5 := { lost := (rows 0 0 3 4 0), upper := (rows 19 7 28 11 20), lower := (rows 19 7 28 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 30), good := (rows 18 22 28 30 16) },{ target := 1, region := (rows 1 0 12 8 30), good := (rows 17 21 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 24 11 16) }] }

theorem profile4_node76 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 3 profile4_node76_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,3] 3 profile4_node76_cert).mp (by decide +kernel))

def profile4_node77_cert : CutBound 5 := { lost := (rows 0 0 3 2 0), upper := (rows 19 7 28 13 18), lower := (rows 19 7 28 13 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 18 22 28 28 16) },{ target := 1, region := (rows 1 0 5 11 16), good := (rows 29 13 28 13 16) }] }

theorem profile4_node77 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 3 profile4_node77_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,5] 3 profile4_node77_cert).mp (by decide +kernel))

def profile4_node78_cert : CutBound 5 := { lost := (rows 0 0 3 1 0), upper := (rows 19 7 28 14 17), lower := (rows 19 7 28 14 16), losses := [{ target := 0, region := (rows 0 2 5 11 16), good := (rows 30 14 28 14 16) },{ target := 1, region := (rows 1 0 12 8 19), good := (rows 17 21 28 28 16) }] }

theorem profile4_node78 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 3 profile4_node78_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24,6] 3 profile4_node78_cert).mp (by decide +kernel))

def profile4_node75_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node75 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] 3 (by decide) (choices 2) [3,5,6] profile4_node75_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5,24] (choices 2) [3,5,6] profile4_node75_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node76
  · exact profile4_node77
  · exact profile4_node78

def profile4_node65_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node65 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile4_node65_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,5] (choices 2) [3,9,10,17,18,24] profile4_node65_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node66
  · exact profile4_node67
  · exact profile4_node70
  · exact profile4_node73
  · exact profile4_node74
  · exact profile4_node75

def profile4_node80_cert : CutBound 5 := { lost := (rows 0 0 16 3 0), upper := (rows 19 11 7 28 20), lower := (rows 19 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 18 10 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 17 9 29 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile4_node80 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 3 profile4_node80_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,3] 3 profile4_node80_cert).mp (by decide +kernel))

def profile4_node81_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 19 11 21 14 22), lower := (rows 19 11 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 4, region := (rows 1 6 4 12 0), good := (rows 3 11 15 8 0) }] }

theorem profile4_node81 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 3 profile4_node81_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,17] 3 profile4_node81_cert).mp (by decide +kernel))

def profile4_node83_cert : CutBound 5 := { lost := (rows 4 4 1 0 0), upper := (rows 19 11 22 13 20), lower := (rows 19 11 22 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 31), good := (rows 22 30 22 28 16) },{ target := 2, region := (rows 5 10 0 8 16), good := (rows 19 11 19 11 16) }] }

theorem profile4_node83 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18,5] 3 profile4_node83_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18,5] 3 profile4_node83_cert).mp (by decide +kernel))

def profile4_node82_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node82 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] 3 (by decide) (choices 2) [5] profile4_node82_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9,18] (choices 2) [5] profile4_node82_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node83

def profile4_node79_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node79 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] 3 (by decide) (choices 2) [3,17,18] profile4_node79_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,9] (choices 2) [3,17,18] profile4_node79_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node80
  · exact profile4_node81
  · exact profile4_node82

def profile4_node86_cert : CutBound 5 := { lost := (rows 0 16 16 6 0), upper := (rows 19 14 7 25 20), lower := (rows 19 14 7 25 16), losses := [{ target := 1, region := (rows 1 0 4 13 22), good := (rows 25 28 29 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 10 11 25 16) },{ target := 4, region := (rows 1 10 13 8 0), good := (rows 7 14 7 15 0) }] }

theorem profile4_node86 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,17] 3 profile4_node86_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,17] 3 profile4_node86_cert).mp (by decide +kernel))

def profile4_node87_cert : CutBound 5 := { lost := (rows 4 1 0 2 0), upper := (rows 19 14 7 28 17), lower := (rows 19 14 7 28 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 18 14 6 30 16) },{ target := 1, region := (rows 1 0 4 14 21), good := (rows 25 28 29 28 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 19 27 19 25 16) }] }

theorem profile4_node87 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,20] 3 profile4_node87_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3,20] 3 profile4_node87_cert).mp (by decide +kernel))

def profile4_node85_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node85 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] 3 (by decide) (choices 2) [17,20] profile4_node85_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,3] (choices 2) [17,20] profile4_node85_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node86
  · exact profile4_node87

def profile4_node88_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 19 14 21 15 23), lower := (rows 19 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 4, region := (rows 1 6 4 12 0), good := (rows 3 14 15 8 0) }] }

theorem profile4_node88 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 3 profile4_node88_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,17] 3 profile4_node88_cert).mp (by decide +kernel))

def profile4_node90_cert : CutBound 5 := { lost := (rows 4 1 1 0 0), upper := (rows 19 14 22 13 17), lower := (rows 19 14 22 13 16), losses := [{ target := 0, region := (rows 0 10 5 8 16), good := (rows 22 14 22 14 16) },{ target := 2, region := (rows 7 2 0 8 31), good := (rows 19 27 19 25 16) }] }

theorem profile4_node90 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18,5] 3 profile4_node90_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18,5] 3 profile4_node90_cert).mp (by decide +kernel))

def profile4_node89_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node89 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] 3 (by decide) (choices 2) [5] profile4_node89_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12,18] (choices 2) [5] profile4_node89_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node90

def profile4_node84_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node84 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] 3 (by decide) (choices 2) [3,17,18] profile4_node84_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,12] (choices 2) [3,17,18] profile4_node84_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node85
  · exact profile4_node88
  · exact profile4_node89

def profile4_node91_cert : CutBound 5 := { lost := (rows 4 4 16 16 0), upper := (rows 19 19 15 15 31), lower := (rows 19 19 4 8 16), losses := [{ target := 2, region := (rows 19 19 0 8 16), good := (rows 19 19 0 8 19) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile4_node91 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 3 profile4_node91_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,17] 3 profile4_node91_cert).mp (by decide +kernel))

def profile4_node92_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 19 22 15 15 31), lower := (rows 19 22 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 19 19 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile4_node92 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 3 profile4_node92_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,20] 3 profile4_node92_cert).mp (by decide +kernel))

def profile4_node93_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 19 26 7 15 23), lower := (rows 19 26 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 19 27 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile4_node93 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 3 profile4_node93_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18,24] 3 profile4_node93_cert).mp (by decide +kernel))

def profile4_node64_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node64 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile4_node64_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [18] (choices 2) [5,9,12,17,20,24] profile4_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node65
  · exact profile4_node79
  · exact profile4_node84
  · exact profile4_node91
  · exact profile4_node92
  · exact profile4_node93

def profile4_node96_cert : CutBound 5 := { lost := (rows 0 16 16 1 0), upper := (rows 25 7 7 30 22), lower := (rows 25 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 24 30 30 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile4_node96 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 3 profile4_node96_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,3] 3 profile4_node96_cert).mp (by decide +kernel))

def profile4_node97_cert : CutBound 5 := { lost := (rows 0 16 2 17 0), upper := (rows 25 7 21 14 22), lower := (rows 25 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 24 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 21 8 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 9 15 15 8 0) }] }

theorem profile4_node97 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 3 profile4_node97_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,17] 3 profile4_node97_cert).mp (by decide +kernel))

def profile4_node99_cert : CutBound 5 := { lost := (rows 6 0 1 4 0), upper := (rows 25 7 22 11 20), lower := (rows 25 7 22 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 31), good := (rows 28 22 22 30 16) },{ target := 1, region := (rows 9 0 4 8 22), good := (rows 25 21 20 25 16) },{ target := 2, region := (rows 5 2 0 14 16), good := (rows 25 11 27 11 16) }] }

theorem profile4_node99 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 3 profile4_node99_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,3] 3 profile4_node99_cert).mp (by decide +kernel))

def profile4_node100_cert : CutBound 5 := { lost := (rows 2 0 1 2 0), upper := (rows 25 7 22 13 18), lower := (rows 25 7 22 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 24 22 22 28 16) },{ target := 1, region := (rows 5 0 4 14 16), good := (rows 25 13 29 13 16) }] }

theorem profile4_node100 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 3 profile4_node100_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,5] 3 profile4_node100_cert).mp (by decide +kernel))

def profile4_node101_cert : CutBound 5 := { lost := (rows 6 0 0 1 0), upper := (rows 25 7 22 14 17), lower := (rows 25 7 22 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 24 14 30 14 16) },{ target := 1, region := (rows 9 0 4 8 27), good := (rows 25 21 20 29 16) },{ target := 2, region := (rows 9 2 0 8 27), good := (rows 25 19 18 27 16) }] }

theorem profile4_node101 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 3 profile4_node101_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18,6] 3 profile4_node101_cert).mp (by decide +kernel))

def profile4_node98_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node98 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] 3 (by decide) (choices 2) [3,5,6] profile4_node98_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5,18] (choices 2) [3,5,6] profile4_node98_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node99
  · exact profile4_node100
  · exact profile4_node101

def profile4_node95_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node95 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] 3 (by decide) (choices 2) [3,17,18] profile4_node95_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,5] (choices 2) [3,17,18] profile4_node95_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node96
  · exact profile4_node97
  · exact profile4_node98

def profile4_node102_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 25 19 7 15 23), lower := (rows 25 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 9 15 4 8 0) }] }

theorem profile4_node102 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 3 profile4_node102_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,17] 3 profile4_node102_cert).mp (by decide +kernel))

def profile4_node105_cert : CutBound 5 := { lost := (rows 6 1 0 4 0), upper := (rows 25 22 7 11 20), lower := (rows 25 22 7 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 22), good := (rows 24 22 22 26 16) },{ target := 1, region := (rows 9 0 4 8 22), good := (rows 25 20 21 25 16) },{ target := 2, region := (rows 3 2 0 14 16), good := (rows 25 27 11 11 16) }] }

theorem profile4_node105 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 3 profile4_node105_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,3] 3 profile4_node105_cert).mp (by decide +kernel))

def profile4_node106_cert : CutBound 5 := { lost := (rows 2 1 0 2 0), upper := (rows 25 22 7 13 18), lower := (rows 25 22 7 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 31), good := (rows 26 22 22 30 16) },{ target := 1, region := (rows 3 0 4 14 16), good := (rows 25 29 13 13 16) }] }

theorem profile4_node106 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 3 profile4_node106_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,5] 3 profile4_node106_cert).mp (by decide +kernel))

def profile4_node107_cert : CutBound 5 := { lost := (rows 6 0 0 1 0), upper := (rows 25 22 7 14 17), lower := (rows 25 22 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 24 30 14 14 16) },{ target := 1, region := (rows 9 0 4 8 29), good := (rows 25 20 21 29 16) },{ target := 2, region := (rows 9 2 0 8 29), good := (rows 25 18 19 27 16) }] }

theorem profile4_node107 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 3 profile4_node107_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3,6] 3 profile4_node107_cert).mp (by decide +kernel))

def profile4_node104_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node104 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] 3 (by decide) (choices 2) [3,5,6] profile4_node104_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20,3] (choices 2) [3,5,6] profile4_node104_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node105
  · exact profile4_node106
  · exact profile4_node107

def profile4_node103_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node103 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] 3 (by decide) (choices 2) [3] profile4_node103_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24,20] (choices 2) [3] profile4_node103_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node104

def profile4_node94_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node94 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] 3 (by decide) (choices 2) [5,17,20] profile4_node94_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [24] (choices 2) [5,17,20] profile4_node94_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node95
  · exact profile4_node102
  · exact profile4_node103

def profile4_node0_route : Route 5 := (fun mask => match mask with | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 3 (by decide) (choices 2) [6,10,18,24] profile4_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] (choices 2) [6,10,18,24] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node45
  · exact profile4_node64
  · exact profile4_node94

theorem profile4 : Upper (D (n:=5) [34,34,34,33,18]) (R (n:=5) [34,34,34,33,18]) [] 3 := profile4_node0

def profile5_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 19 21 26 26), lower := (rows 7 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 26 28 8 16) }] }

theorem profile5_node3 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,17] 3 profile5_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,17] 3 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 19 22 25 25), lower := (rows 7 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 22 22 8 16) }] }

theorem profile5_node4 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,18] 3 profile5_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,18] 3 profile5_node4_cert).mp (by decide +kernel))

def profile5_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 19 28 25 18), lower := (rows 7 19 28 25 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 22 18 28 28 16) }] }

theorem profile5_node6 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,17] 3 profile5_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,17] 3 profile5_node6_cert).mp (by decide +kernel))

def profile5_node7_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 7 19 28 26 17), lower := (rows 7 19 28 26 16), losses := [{ target := 0, region := (rows 0 2 14 10 16), good := (rows 14 30 28 30 16) }] }

theorem profile5_node7 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,18] 3 profile5_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24,18] 3 profile5_node7_cert).mp (by decide +kernel))

def profile5_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node5 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24] 3 (by decide) (choices 2) [17,18] profile5_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17,24] (choices 2) [17,18] profile5_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node6
  · exact profile5_node7

def profile5_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node2 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17] 3 (by decide) (choices 2) [17,18,24] profile5_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,17] (choices 2) [17,18,24] profile5_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node3
  · exact profile5_node4
  · exact profile5_node5

def profile5_node10_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 7 26 21 25 18), lower := (rows 7 26 21 25 16), losses := [{ target := 0, region := (rows 0 10 4 8 27), good := (rows 22 26 20 26 16) }] }

theorem profile5_node10 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,17] 3 profile5_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,17] 3 profile5_node10_cert).mp (by decide +kernel))

def profile5_node11_cert : CutBound 5 := { lost := (rows 0 1 0 1 0), upper := (rows 7 26 21 26 17), lower := (rows 7 26 21 26 16), losses := [{ target := 0, region := (rows 0 30 4 30 16), good := (rows 14 26 30 26 26) }] }

theorem profile5_node11 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,18] 3 profile5_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17,18] 3 profile5_node11_cert).mp (by decide +kernel))

def profile5_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node9 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17] 3 (by decide) (choices 2) [17,18] profile5_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,17] (choices 2) [17,18] profile5_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node10
  · exact profile5_node11

def profile5_node12_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 7 26 22 25 17), lower := (rows 7 26 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 22 8 16) }] }

theorem profile5_node12 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,18] 3 profile5_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24,18] 3 profile5_node12_cert).mp (by decide +kernel))

def profile5_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node8 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24] 3 (by decide) (choices 2) [17,18] profile5_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6,24] (choices 2) [17,18] profile5_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node9
  · exact profile5_node12

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6] 3 (by decide) (choices 2) [17,24] profile5_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [6] (choices 2) [17,24] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node2
  · exact profile5_node8

def profile5_node15_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 13 19 21 26 18), lower := (rows 13 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 12 26 20 8 16) }] }

theorem profile5_node15 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,17] 3 profile5_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,17] 3 profile5_node15_cert).mp (by decide +kernel))

def profile5_node16_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 13 19 22 27 19), lower := (rows 13 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 12 22 22 8 16) }] }

theorem profile5_node16 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,18] 3 profile5_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17,18] 3 profile5_node16_cert).mp (by decide +kernel))

def profile5_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node14 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17] 3 (by decide) (choices 2) [17,18] profile5_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12,17] (choices 2) [17,18] profile5_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node15
  · exact profile5_node16

def profile5_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node13 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12] 3 (by decide) (choices 2) [17] profile5_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [12] (choices 2) [17] profile5_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node14

def profile5_node19_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 7 21 26 26), lower := (rows 19 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 26 30 28 8 16) }] }

theorem profile5_node19 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,17] 3 profile5_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,17] 3 profile5_node19_cert).mp (by decide +kernel))

def profile5_node20_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 7 22 25 25), lower := (rows 19 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 6 22 8 16) }] }

theorem profile5_node20 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,18] 3 profile5_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,18] 3 profile5_node20_cert).mp (by decide +kernel))

def profile5_node22_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 7 28 25 18), lower := (rows 19 7 28 25 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 18 22 28 28 16) }] }

theorem profile5_node22 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,17] 3 profile5_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,17] 3 profile5_node22_cert).mp (by decide +kernel))

def profile5_node23_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 19 7 28 26 17), lower := (rows 19 7 28 26 16), losses := [{ target := 0, region := (rows 0 2 13 9 16), good := (rows 30 14 28 30 16) }] }

theorem profile5_node23 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,18] 3 profile5_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24,18] 3 profile5_node23_cert).mp (by decide +kernel))

def profile5_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node21 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24] 3 (by decide) (choices 2) [17,18] profile5_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5,24] (choices 2) [17,18] profile5_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node22
  · exact profile5_node23

def profile5_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node18 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5] 3 (by decide) (choices 2) [17,18,24] profile5_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,5] (choices 2) [17,18,24] profile5_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node19
  · exact profile5_node20
  · exact profile5_node21

def profile5_node25_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 19 14 21 27 19), lower := (rows 19 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) }] }

theorem profile5_node25 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,17] 3 profile5_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,17] 3 profile5_node25_cert).mp (by decide +kernel))

def profile5_node26_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 14 22 25 17), lower := (rows 19 14 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) }] }

theorem profile5_node26 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,18] 3 profile5_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12,18] 3 profile5_node26_cert).mp (by decide +kernel))

def profile5_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node24 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12] 3 (by decide) (choices 2) [17,18] profile5_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,12] (choices 2) [17,18] profile5_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node25
  · exact profile5_node26

def profile5_node28_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 19 7 28 28), lower := (rows 19 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 18 18 30 8 16) }] }

theorem profile5_node28 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,3] 3 profile5_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,3] 3 profile5_node28_cert).mp (by decide +kernel))

def profile5_node30_cert : Bound 5 := { allowed := (rows 0 0 18 1 0), upper := (rows 19 19 13 26 20), lower := (rows 19 19 13 26 16), losses := [] }

theorem profile5_node30 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,18] 3 :=
  bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,18] 3 profile5_node30_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,18] 3 profile5_node30_cert).mp (by decide +kernel))

def profile5_node31_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 19 13 28 18), lower := (rows 19 19 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 19), good := (rows 18 18 28 28 16) }] }

theorem profile5_node31 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,20] 3 profile5_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9,20] 3 profile5_node31_cert).mp (by decide +kernel))

def profile5_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node29 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9] 3 (by decide) (choices 2) [18,20] profile5_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,9] (choices 2) [18,20] profile5_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node30
  · exact profile5_node31

def profile5_node33_cert : Bound 5 := { allowed := (rows 0 0 17 2 0), upper := (rows 19 19 14 25 20), lower := (rows 19 19 14 25 16), losses := [] }

theorem profile5_node33 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,17] 3 :=
  bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,17] 3 profile5_node33_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,17] 3 profile5_node33_cert).mp (by decide +kernel))

def profile5_node34_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 19 19 14 28 17), lower := (rows 19 19 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 11 16), good := (rows 30 30 14 28 16) }] }

theorem profile5_node34 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,20] 3 profile5_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10,20] 3 profile5_node34_cert).mp (by decide +kernel))

def profile5_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node32 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10] 3 (by decide) (choices 2) [17,20] profile5_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,10] (choices 2) [17,20] profile5_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node33
  · exact profile5_node34

def profile5_node35_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 19 19 21 14 30), lower := (rows 19 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 21 21 21 8 16) }] }

theorem profile5_node35 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,17] 3 profile5_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,17] 3 profile5_node35_cert).mp (by decide +kernel))

def profile5_node36_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 19 22 13 29), lower := (rows 19 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 22 22 8 16) }] }

theorem profile5_node36 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,18] 3 profile5_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,18] 3 profile5_node36_cert).mp (by decide +kernel))

def profile5_node38_cert : Bound 5 := { allowed := (rows 0 0 3 16 0), upper := (rows 19 19 28 11 20), lower := (rows 19 19 28 11 16), losses := [] }

theorem profile5_node38 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,3] 3 :=
  bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,3] 3 profile5_node38_cert
    ((SmallBoolean.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,3] 3 profile5_node38_cert).mp (by decide +kernel))

def profile5_node39_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 19 19 28 13 18), lower := (rows 19 19 28 13 16), losses := [{ target := 0, region := (rows 0 2 12 8 19), good := (rows 18 18 28 28 16) }] }

theorem profile5_node39 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,5] 3 profile5_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,5] 3 profile5_node39_cert).mp (by decide +kernel))

def profile5_node40_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 19 19 28 14 17), lower := (rows 19 19 28 14 16), losses := [{ target := 0, region := (rows 0 2 7 11 16), good := (rows 30 30 28 14 16) }] }

theorem profile5_node40 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,6] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,6] 3 profile5_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24,6] 3 profile5_node40_cert).mp (by decide +kernel))

def profile5_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node37 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24] 3 (by decide) (choices 2) [3,5,6] profile5_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17,24] (choices 2) [3,5,6] profile5_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node38
  · exact profile5_node39
  · exact profile5_node40

def profile5_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node27 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile5_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,17] (choices 2) [3,9,10,17,18,24] profile5_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node28
  · exact profile5_node29
  · exact profile5_node32
  · exact profile5_node35
  · exact profile5_node36
  · exact profile5_node37

def profile5_node42_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 19 22 7 25 25), lower := (rows 19 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile5_node42 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,3] 3 profile5_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,3] 3 profile5_node42_cert).mp (by decide +kernel))

def profile5_node44_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 19 22 13 25 18), lower := (rows 19 22 13 25 16), losses := [{ target := 0, region := (rows 0 6 4 8 23), good := (rows 18 22 30 24 16) }] }

theorem profile5_node44 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,17] 3 profile5_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,17] 3 profile5_node44_cert).mp (by decide +kernel))

def profile5_node45_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 19 22 13 26 17), lower := (rows 19 22 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 26 30 12 26 16) }] }

theorem profile5_node45 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,18] 3 profile5_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9,18] 3 profile5_node45_cert).mp (by decide +kernel))

def profile5_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node43 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9] 3 (by decide) (choices 2) [17,18] profile5_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,9] (choices 2) [17,18] profile5_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node44
  · exact profile5_node45

def profile5_node46_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 19 22 14 25 17), lower := (rows 19 22 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 25 20 12 8 16) }] }

theorem profile5_node46 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,10] 3 profile5_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,10] 3 profile5_node46_cert).mp (by decide +kernel))

def profile5_node47_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 19 22 21 11 27), lower := (rows 19 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 18 22 22 8 16) }] }

theorem profile5_node47 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,17] 3 profile5_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,17] 3 profile5_node47_cert).mp (by decide +kernel))

def profile5_node48_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 19 22 22 9 25), lower := (rows 19 22 22 8 16), losses := [{ target := 0, region := (rows 0 23 23 8 16), good := (rows 22 22 22 8 22) }] }

theorem profile5_node48 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,18] 3 profile5_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,18] 3 profile5_node48_cert).mp (by decide +kernel))

def profile5_node49_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 19 22 28 11 19), lower := (rows 19 22 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 18 22 30 8 16) }] }

theorem profile5_node49 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,24] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,24] 3 profile5_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20,24] 3 profile5_node49_cert).mp (by decide +kernel))

def profile5_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node41 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile5_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18,20] (choices 2) [3,9,10,17,18,24] profile5_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node42
  · exact profile5_node43
  · exact profile5_node46
  · exact profile5_node47
  · exact profile5_node48
  · exact profile5_node49

def profile5_node17_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile5_node17 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18] 3 (by decide) (choices 2) [5,12,17,20] profile5_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [18] (choices 2) [5,12,17,20] profile5_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node18
  · exact profile5_node24
  · exact profile5_node27
  · exact profile5_node41

def profile5_node52_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 21 11 21 26 18), lower := (rows 21 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 20 26 20 8 16) }] }

theorem profile5_node52 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,17] 3 profile5_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,17] 3 profile5_node52_cert).mp (by decide +kernel))

def profile5_node53_cert : CutBound 5 := { lost := (rows 2 0 0 0 0), upper := (rows 21 11 22 27 19), lower := (rows 21 11 22 8 16), losses := [{ target := 1, region := (rows 5 0 4 8 16), good := (rows 21 9 21 8 16) }] }

theorem profile5_node53 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,18] 3 profile5_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9,18] 3 profile5_node53_cert).mp (by decide +kernel))

def profile5_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node51 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9] 3 (by decide) (choices 2) [17,18] profile5_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,9] (choices 2) [17,18] profile5_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node52
  · exact profile5_node53

def profile5_node55_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 21 19 7 26 26), lower := (rows 21 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 26 30 8 16) }] }

theorem profile5_node55 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,3] 3 profile5_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,3] 3 profile5_node55_cert).mp (by decide +kernel))

def profile5_node56_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 21 19 13 26 18), lower := (rows 21 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 20 26 12 8 16) }] }

theorem profile5_node56 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,9] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,9] 3 profile5_node56_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,9] 3 profile5_node56_cert).mp (by decide +kernel))

def profile5_node58_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 21 19 14 25 18), lower := (rows 21 19 14 25 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 25 12 25 16) }] }

theorem profile5_node58 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,17] 3 profile5_node58_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,17] 3 profile5_node58_cert).mp (by decide +kernel))

def profile5_node59_cert : CutBound 5 := { lost := (rows 0 0 1 1 0), upper := (rows 21 19 14 26 17), lower := (rows 21 19 14 26 16), losses := [{ target := 0, region := (rows 0 2 14 10 16), good := (rows 20 30 14 30 16) }] }

theorem profile5_node59 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,18] 3 profile5_node59_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10,18] 3 profile5_node59_cert).mp (by decide +kernel))

def profile5_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node57 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10] 3 (by decide) (choices 2) [17,18] profile5_node57_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,10] (choices 2) [17,18] profile5_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node58
  · exact profile5_node59

def profile5_node60_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 21 19 21 10 26), lower := (rows 21 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 20 26 20 8 16) }] }

theorem profile5_node60 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,17] 3 profile5_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,17] 3 profile5_node60_cert).mp (by decide +kernel))

def profile5_node61_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 21 19 22 11 27), lower := (rows 21 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 20 22 22 8 16) }] }

theorem profile5_node61 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,18] 3 profile5_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,18] 3 profile5_node61_cert).mp (by decide +kernel))

def profile5_node62_cert : CutBound 5 := { lost := (rows 2 0 0 0 0), upper := (rows 21 19 28 11 19), lower := (rows 21 19 28 8 16), losses := [{ target := 1, region := (rows 5 0 4 8 16), good := (rows 21 17 29 8 16) }] }

theorem profile5_node62 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,24] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,24] 3 profile5_node62_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17,24] 3 profile5_node62_cert).mp (by decide +kernel))

def profile5_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node54 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile5_node54_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,17] (choices 2) [3,9,10,17,18,24] profile5_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node55
  · exact profile5_node56
  · exact profile5_node57
  · exact profile5_node60
  · exact profile5_node61
  · exact profile5_node62

def profile5_node65_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 21 26 7 25 18), lower := (rows 21 26 7 25 16), losses := [{ target := 0, region := (rows 0 10 4 8 30), good := (rows 20 26 22 26 16) }] }

theorem profile5_node65 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,17] 3 profile5_node65_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,17] 3 profile5_node65_cert).mp (by decide +kernel))

def profile5_node66_cert : CutBound 5 := { lost := (rows 0 1 0 1 0), upper := (rows 21 26 7 26 17), lower := (rows 21 26 7 26 16), losses := [{ target := 0, region := (rows 0 27 4 27 16), good := (rows 30 26 14 26 26) }] }

theorem profile5_node66 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,18] 3 profile5_node66_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3,18] 3 profile5_node66_cert).mp (by decide +kernel))

def profile5_node64_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node64 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3] 3 (by decide) (choices 2) [17,18] profile5_node64_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,3] (choices 2) [17,18] profile5_node64_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile5_node65
  · exact profile5_node66

def profile5_node67_cert : CutBound 5 := { lost := (rows 2 0 2 0 0), upper := (rows 21 26 21 11 19), lower := (rows 21 26 21 8 16), losses := [{ target := 1, region := (rows 23 0 23 8 16), good := (rows 21 29 21 8 21) }] }

theorem profile5_node67 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,17] 3 profile5_node67_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,17] 3 profile5_node67_cert).mp (by decide +kernel))

def profile5_node68_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 21 26 22 11 19), lower := (rows 21 26 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 20 30 22 8 16) }] }

theorem profile5_node68 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,18] 3 profile5_node68_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24,18] 3 profile5_node68_cert).mp (by decide +kernel))

def profile5_node63_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node63 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24] 3 (by decide) (choices 2) [3,17,18] profile5_node63_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20,24] (choices 2) [3,17,18] profile5_node63_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node64
  · exact profile5_node67
  · exact profile5_node68

def profile5_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node50 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20] 3 (by decide) (choices 2) [9,17,24] profile5_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [20] (choices 2) [9,17,24] profile5_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node51
  · exact profile5_node54
  · exact profile5_node63

def profile5_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [] 3 (by decide) (choices 2) [6,12,18,20] profile5_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [] (choices 2) [6,12,18,20] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node1
  · exact profile5_node13
  · exact profile5_node17
  · exact profile5_node50

theorem profile5 : Upper (D (n:=5) [34,34,33,33,19]) (R (n:=5) [34,34,33,33,19]) [] 3 := profile5_node0

#print axioms profile5
end Delivery.FiveVertexPositive09
