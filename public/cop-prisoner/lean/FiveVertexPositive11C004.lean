import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile38_node4_cert : CutBound 5 := { lost := (rows 0 8 8 4 2), upper := (rows 15 7 22 26 28), lower := (rows 15 7 22 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 20 24 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 26 26 16) },{ target := 3, region := (rows 1 3 12 0 16), good := (rows 7 7 22 22 16) }] }

theorem profile38_node4 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,18] 3 profile38_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,18] 3 profile38_node4_cert).mp (by decide +kernel))

def profile38_node5_cert : CutBound 5 := { lost := (rows 0 8 0 2 4), upper := (rows 15 7 22 28 26), lower := (rows 15 7 22 28 16), losses := [{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 28 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 18 24 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 22 20 16) }] }

theorem profile38_node5 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,20] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,20] 3 profile38_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18,20] 3 profile38_node5_cert).mp (by decide +kernel))

def profile38_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node3 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18] 3 (by decide) (choices 2) [18,20] profile38_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,18] (choices 2) [18,20] profile38_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node4
  · exact profile38_node5

def profile38_node6_cert : CutBound 5 := { lost := (rows 16 24 0 0 8), upper := (rows 15 7 28 30 22), lower := (rows 15 7 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 5 7 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile38_node6 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,24] 3 profile38_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5,24] 3 profile38_node6_cert).mp (by decide +kernel))

def profile38_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node2 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5] 3 (by decide) (choices 2) [18,24] profile38_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,5] (choices 2) [18,24] profile38_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node3
  · exact profile38_node6

def profile38_node7_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 15 11 22 30 22), lower := (rows 15 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 11 11 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile38_node7 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,9] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,9] 3 profile38_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,9] 3 profile38_node7_cert).mp (by decide +kernel))

def profile38_node8_cert : CutBound 5 := { lost := (rows 16 16 8 0 8), upper := (rows 15 14 23 31 23), lower := (rows 15 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile38_node8 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,12] 3 profile38_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,12] 3 profile38_node8_cert).mp (by decide +kernel))

def profile38_node10_cert : CutBound 5 := { lost := (rows 16 8 16 0 8), upper := (rows 15 19 14 30 22), lower := (rows 15 19 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 21), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile38_node10 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,10] 3 profile38_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,10] 3 profile38_node10_cert).mp (by decide +kernel))

def profile38_node11_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 19 22 14 30), lower := (rows 15 19 22 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile38_node11 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,18] 3 profile38_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,18] 3 profile38_node11_cert).mp (by decide +kernel))

def profile38_node12_cert : CutBound 5 := { lost := (rows 0 8 0 16 8), upper := (rows 15 19 28 14 22), lower := (rows 15 19 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 20 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile38_node12 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,24] 3 profile38_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17,24] 3 profile38_node12_cert).mp (by decide +kernel))

def profile38_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node9 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17] 3 (by decide) (choices 2) [10,18,24] profile38_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,17] (choices 2) [10,18,24] profile38_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node10
  · exact profile38_node11
  · exact profile38_node12

def profile38_node15_cert : CutBound 5 := { lost := (rows 0 0 8 4 2), upper := (rows 15 22 7 26 28), lower := (rows 15 22 7 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 20 21 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 26 11 26 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 18 16) }] }

theorem profile38_node15 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,18] 3 profile38_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,18] 3 profile38_node15_cert).mp (by decide +kernel))

def profile38_node16_cert : CutBound 5 := { lost := (rows 0 8 8 2 4), upper := (rows 15 22 7 28 26), lower := (rows 15 22 7 28 16), losses := [{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 28 13 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 18 19 24 16) },{ target := 3, region := (rows 1 10 5 0 16), good := (rows 7 22 7 22 16) }] }

theorem profile38_node16 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,20] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,20] 3 profile38_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3,20] 3 profile38_node16_cert).mp (by decide +kernel))

def profile38_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node14 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3] 3 (by decide) (choices 2) [18,20] profile38_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,3] (choices 2) [18,20] profile38_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node15
  · exact profile38_node16

def profile38_node17_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 22 13 30 22), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 22 23 0 16) }] }

theorem profile38_node17 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,9] 3 profile38_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,9] 3 profile38_node17_cert).mp (by decide +kernel))

def profile38_node18_cert : CutBound 5 := { lost := (rows 16 8 16 0 8), upper := (rows 15 22 14 31 23), lower := (rows 15 22 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile38_node18 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,10] 3 profile38_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,10] 3 profile38_node18_cert).mp (by decide +kernel))

def profile38_node19_cert : CutBound 5 := { lost := (rows 16 8 0 16 0), upper := (rows 15 22 21 14 30), lower := (rows 15 22 21 8 16), losses := [{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile38_node19 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,17] 3 profile38_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,17] 3 profile38_node19_cert).mp (by decide +kernel))

def profile38_node20_cert : CutBound 5 := { lost := (rows 16 8 8 16 0), upper := (rows 15 22 22 15 31), lower := (rows 15 22 22 8 16), losses := [{ target := 3, region := (rows 1 22 22 0 16), good := (rows 7 22 22 0 22) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile38_node20 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,18] 3 profile38_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,18] 3 profile38_node20_cert).mp (by decide +kernel))

def profile38_node21_cert : CutBound 5 := { lost := (rows 16 8 0 16 8), upper := (rows 15 22 28 15 23), lower := (rows 15 22 28 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile38_node21 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,24] 3 profile38_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20,24] 3 profile38_node21_cert).mp (by decide +kernel))

def profile38_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node13 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile38_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,20] (choices 2) [3,9,10,17,18,24] profile38_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile38_node14
  · exact profile38_node17
  · exact profile38_node18
  · exact profile38_node19
  · exact profile38_node20
  · exact profile38_node21

def profile38_node23_cert : CutBound 5 := { lost := (rows 16 0 24 0 8), upper := (rows 15 26 7 30 22), lower := (rows 15 26 7 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 18 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile38_node23 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,3] 3 profile38_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,3] 3 profile38_node23_cert).mp (by decide +kernel))

def profile38_node24_cert : CutBound 5 := { lost := (rows 0 0 8 16 8), upper := (rows 15 26 21 14 22), lower := (rows 15 26 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 18 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 10 13 8 0) }] }

theorem profile38_node24 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,17] 3 profile38_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,17] 3 profile38_node24_cert).mp (by decide +kernel))

def profile38_node25_cert : CutBound 5 := { lost := (rows 16 0 8 16 8), upper := (rows 15 26 22 15 23), lower := (rows 15 26 22 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 10 15 8 0) }] }

theorem profile38_node25 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,18] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,18] 3 profile38_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24,18] 3 profile38_node25_cert).mp (by decide +kernel))

def profile38_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node22 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24] 3 (by decide) (choices 2) [3,17,18] profile38_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14,24] (choices 2) [3,17,18] profile38_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node23
  · exact profile38_node24
  · exact profile38_node25

def profile38_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile38_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [14] (choices 2) [5,9,12,17,20,24] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile38_node2
  · exact profile38_node7
  · exact profile38_node8
  · exact profile38_node9
  · exact profile38_node13
  · exact profile38_node22

def profile38_node28_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 27 7 14 30 22), lower := (rows 27 7 14 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 22), good := (rows 19 23 22 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile38_node28 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,10] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,10] 3 profile38_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,10] 3 profile38_node28_cert).mp (by decide +kernel))

def profile38_node29_cert : CutBound 5 := { lost := (rows 0 0 2 16 8), upper := (rows 27 7 28 14 22), lower := (rows 27 7 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 28 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 20 0 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 12 8 0) }] }

theorem profile38_node29 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,24] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,24] 3 profile38_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5,24] 3 profile38_node29_cert).mp (by decide +kernel))

def profile38_node27_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile38_node27 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5] 3 (by decide) (choices 2) [10,24] profile38_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,5] (choices 2) [10,24] profile38_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node28
  · exact profile38_node29

def profile38_node31_cert : CutBound 5 := { lost := (rows 0 16 24 0 8), upper := (rows 27 14 7 30 22), lower := (rows 27 14 7 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 23), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile38_node31 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,3] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,3] 3 profile38_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,3] 3 profile38_node31_cert).mp (by decide +kernel))

def profile38_node32_cert : CutBound 5 := { lost := (rows 0 0 10 0 8), upper := (rows 27 14 21 14 22), lower := (rows 27 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 21 8 16) },{ target := 3, region := (rows 1 2 5 0 19), good := (rows 23 22 21 0 16) }] }

theorem profile38_node32 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,17] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,17] 3 profile38_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,17] 3 profile38_node32_cert).mp (by decide +kernel))

def profile38_node34_cert : CutBound 5 := { lost := (rows 0 16 8 0 8), upper := (rows 27 14 22 13 22), lower := (rows 27 14 22 13 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 22 22 21 16) },{ target := 4, region := (rows 1 10 4 8 0), good := (rows 11 14 6 15 0) }] }

theorem profile38_node34 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,5] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,5] 3 profile38_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,5] 3 profile38_node34_cert).mp (by decide +kernel))

def profile38_node35_cert : CutBound 5 := { lost := (rows 0 16 8 16 8), upper := (rows 27 14 22 14 21), lower := (rows 27 14 22 14 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 22 6 16) },{ target := 4, region := (rows 1 14 4 14 0), good := (rows 11 14 14 14 0) }] }

theorem profile38_node35 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,6] 3 :=
  cut_bound_sound (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,6] 3 profile38_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18,6] 3 profile38_node35_cert).mp (by decide +kernel))

def profile38_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node33 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18] 3 (by decide) (choices 2) [5,6] profile38_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12,18] (choices 2) [5,6] profile38_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node34
  · exact profile38_node35

def profile38_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node30 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12] 3 (by decide) (choices 2) [3,17,18] profile38_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26,12] (choices 2) [3,17,18] profile38_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node31
  · exact profile38_node32
  · exact profile38_node33

def profile38_node26_route : Route 5 := (fun mask => match mask with | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile38_node26 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26] 3 (by decide) (choices 2) [5,12] profile38_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [26] (choices 2) [5,12] profile38_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node27
  · exact profile38_node30

def profile38_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile38_node0 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [] 3 := by
  apply routed_branch (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [] 3 (by decide) (choices 3) [14,26] profile38_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [] (choices 3) [14,26] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile38_node1
  · exact profile38_node26

theorem profile38 : Upper (D (n:=5) [49,35,35,34,34]) (R (n:=5) [49,35,35,34,34]) [] 3 := profile38_node0

#print axioms profile38
end Delivery.FiveVertexPositive11
