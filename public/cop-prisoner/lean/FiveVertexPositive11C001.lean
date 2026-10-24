import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile15_node2_cert : CutBound 5 := { lost := (rows 16 16 8 0 0), upper := (rows 15 15 23 31 23), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile15_node2 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,13] 3 profile15_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,13] 3 profile15_node2_cert).mp (by decide +kernel))

def profile15_node4_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 15 23 7 28 28), lower := (rows 15 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile15_node4 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,3] 3 profile15_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,3] 3 profile15_node4_cert).mp (by decide +kernel))

def profile15_node5_cert : CutBound 5 := { lost := (rows 0 8 2 1 0), upper := (rows 15 23 13 30 22), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile15_node5 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,9] 3 profile15_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,9] 3 profile15_node5_cert).mp (by decide +kernel))

def profile15_node6_cert : CutBound 5 := { lost := (rows 0 8 1 2 0), upper := (rows 15 23 14 29 21), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile15_node6 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,10] 3 profile15_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,10] 3 profile15_node6_cert).mp (by decide +kernel))

def profile15_node7_cert : CutBound 5 := { lost := (rows 0 8 10 1 0), upper := (rows 15 23 21 14 30), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile15_node7 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,17] 3 profile15_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,17] 3 profile15_node7_cert).mp (by decide +kernel))

def profile15_node8_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 15 23 22 13 29), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) }] }

theorem profile15_node8 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,18] 3 profile15_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,18] 3 profile15_node8_cert).mp (by decide +kernel))

def profile15_node9_cert : CutBound 5 := { lost := (rows 16 8 0 16 0), upper := (rows 15 23 28 15 23), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile15_node9 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,24] 3 profile15_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21,24] 3 profile15_node9_cert).mp (by decide +kernel))

def profile15_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node3 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile15_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,21] (choices 2) [3,9,10,17,18,24] profile15_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node4
  · exact profile15_node5
  · exact profile15_node6
  · exact profile15_node7
  · exact profile15_node8
  · exact profile15_node9

def profile15_node11_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 15 27 7 28 20), lower := (rows 15 27 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile15_node11 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,3] 3 profile15_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,3] 3 profile15_node11_cert).mp (by decide +kernel))

def profile15_node12_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 15 27 21 14 22), lower := (rows 15 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile15_node12 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,17] 3 profile15_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,17] 3 profile15_node12_cert).mp (by decide +kernel))

def profile15_node13_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 15 27 22 13 21), lower := (rows 15 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile15_node13 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,18] 3 profile15_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25,18] 3 profile15_node13_cert).mp (by decide +kernel))

def profile15_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node10 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25] 3 (by decide) (choices 2) [3,17,18] profile15_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,25] (choices 2) [3,17,18] profile15_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node11
  · exact profile15_node12
  · exact profile15_node13

def profile15_node15_cert : CutBound 5 := { lost := (rows 16 0 24 2 0), upper := (rows 15 30 7 29 21), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile15_node15 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,3] 3 profile15_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,3] 3 profile15_node15_cert).mp (by decide +kernel))

def profile15_node16_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 30 21 15 23), lower := (rows 15 30 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile15_node16 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,17] 3 profile15_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,17] 3 profile15_node16_cert).mp (by decide +kernel))

def profile15_node17_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 15 30 22 13 21), lower := (rows 15 30 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) },{ target := 3, region := (rows 1 2 7 0 17), good := (rows 23 22 22 0 16) }] }

theorem profile15_node17 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,18] 3 profile15_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28,18] 3 profile15_node17_cert).mp (by decide +kernel))

def profile15_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node14 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28] 3 (by decide) (choices 2) [3,17,18] profile15_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14,28] (choices 2) [3,17,18] profile15_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node15
  · exact profile15_node16
  · exact profile15_node17

def profile15_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14] 3 (by decide) (choices 3) [13,21,25,28] profile15_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [14] (choices 3) [13,21,25,28] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node2
  · exact profile15_node3
  · exact profile15_node10
  · exact profile15_node14

def profile15_node20_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 23 15 7 28 28), lower := (rows 23 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile15_node20 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,3] 3 profile15_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,3] 3 profile15_node20_cert).mp (by decide +kernel))

def profile15_node21_cert : CutBound 5 := { lost := (rows 8 0 2 1 0), upper := (rows 23 15 13 30 22), lower := (rows 23 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile15_node21 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,9] 3 profile15_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,9] 3 profile15_node21_cert).mp (by decide +kernel))

def profile15_node22_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 15 14 29 21), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile15_node22 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,10] 3 profile15_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,10] 3 profile15_node22_cert).mp (by decide +kernel))

def profile15_node23_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 23 15 21 14 30), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) }] }

theorem profile15_node23 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,17] 3 profile15_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,17] 3 profile15_node23_cert).mp (by decide +kernel))

def profile15_node24_cert : CutBound 5 := { lost := (rows 8 0 9 2 0), upper := (rows 23 15 22 13 29), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile15_node24 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,18] 3 profile15_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,18] 3 profile15_node24_cert).mp (by decide +kernel))

def profile15_node25_cert : CutBound 5 := { lost := (rows 8 16 0 16 0), upper := (rows 23 15 28 15 23), lower := (rows 23 15 28 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile15_node25 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,24] 3 profile15_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13,24] 3 profile15_node25_cert).mp (by decide +kernel))

def profile15_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node19 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile15_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,13] (choices 2) [3,9,10,17,18,24] profile15_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node20
  · exact profile15_node21
  · exact profile15_node22
  · exact profile15_node23
  · exact profile15_node24
  · exact profile15_node25

def profile15_node26_cert : CutBound 5 := { lost := (rows 8 8 16 16 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile15_node26 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,21] 3 profile15_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,21] 3 profile15_node26_cert).mp (by decide +kernel))

def profile15_node28_cert : CutBound 5 := { lost := (rows 8 0 8 3 0), upper := (rows 23 27 7 12 28), lower := (rows 23 27 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile15_node28 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,3] 3 profile15_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,3] 3 profile15_node28_cert).mp (by decide +kernel))

def profile15_node29_cert : CutBound 5 := { lost := (rows 0 0 18 17 0), upper := (rows 23 27 13 14 22), lower := (rows 23 27 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 13 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile15_node29 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,9] 3 profile15_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,9] 3 profile15_node29_cert).mp (by decide +kernel))

def profile15_node30_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 14 13 21), lower := (rows 23 27 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile15_node30 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,10] 3 profile15_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25,10] 3 profile15_node30_cert).mp (by decide +kernel))

def profile15_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node27 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25] 3 (by decide) (choices 2) [3,9,10] profile15_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,25] (choices 2) [3,9,10] profile15_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node28
  · exact profile15_node29
  · exact profile15_node30

def profile15_node31_cert : CutBound 5 := { lost := (rows 8 0 16 16 0), upper := (rows 23 30 15 15 31), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile15_node31 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,28] 3 profile15_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22,28] 3 profile15_node31_cert).mp (by decide +kernel))

def profile15_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node18 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile15_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [22] (choices 3) [13,21,25,28] profile15_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node19
  · exact profile15_node26
  · exact profile15_node27
  · exact profile15_node31

def profile15_node34_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 27 15 7 28 20), lower := (rows 27 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile15_node34 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,3] 3 profile15_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,3] 3 profile15_node34_cert).mp (by decide +kernel))

def profile15_node35_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 27 15 21 14 22), lower := (rows 27 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile15_node35 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,17] 3 profile15_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,17] 3 profile15_node35_cert).mp (by decide +kernel))

def profile15_node36_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 27 15 22 13 21), lower := (rows 27 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile15_node36 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,18] 3 profile15_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13,18] 3 profile15_node36_cert).mp (by decide +kernel))

def profile15_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node33 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13] 3 (by decide) (choices 2) [3,17,18] profile15_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,13] (choices 2) [3,17,18] profile15_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node34
  · exact profile15_node35
  · exact profile15_node36

def profile15_node38_cert : CutBound 5 := { lost := (rows 0 8 8 3 0), upper := (rows 27 23 7 12 28), lower := (rows 27 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile15_node38 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,3] 3 profile15_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,3] 3 profile15_node38_cert).mp (by decide +kernel))

def profile15_node39_cert : CutBound 5 := { lost := (rows 0 8 2 1 0), upper := (rows 27 23 13 14 22), lower := (rows 27 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 12 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) }] }

theorem profile15_node39 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,9] 3 profile15_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,9] 3 profile15_node39_cert).mp (by decide +kernel))

def profile15_node40_cert : CutBound 5 := { lost := (rows 0 0 17 18 0), upper := (rows 27 23 14 13 21), lower := (rows 27 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile15_node40 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,10] 3 profile15_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21,10] 3 profile15_node40_cert).mp (by decide +kernel))

def profile15_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node37 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21] 3 (by decide) (choices 2) [3,9,10] profile15_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,21] (choices 2) [3,9,10] profile15_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node38
  · exact profile15_node39
  · exact profile15_node40

def profile15_node41_cert : CutBound 5 := { lost := (rows 4 0 24 16 0), upper := (rows 27 30 7 15 23), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile15_node41 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,28] 3 profile15_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26,28] 3 profile15_node41_cert).mp (by decide +kernel))

def profile15_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node32 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26] 3 (by decide) (choices 3) [13,21,28] profile15_node32_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [26] (choices 3) [13,21,28] profile15_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node33
  · exact profile15_node37
  · exact profile15_node41

def profile15_node44_cert : CutBound 5 := { lost := (rows 0 16 24 1 0), upper := (rows 29 15 7 30 22), lower := (rows 29 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile15_node44 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,3] 3 profile15_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,3] 3 profile15_node44_cert).mp (by decide +kernel))

def profile15_node45_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 29 15 21 14 22), lower := (rows 29 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 18), good := (rows 21 23 21 0 16) }] }

theorem profile15_node45 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,17] 3 profile15_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,17] 3 profile15_node45_cert).mp (by decide +kernel))

def profile15_node46_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 29 15 22 15 23), lower := (rows 29 15 22 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile15_node46 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,18] 3 profile15_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13,18] 3 profile15_node46_cert).mp (by decide +kernel))

def profile15_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node43 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13] 3 (by decide) (choices 2) [3,17,18] profile15_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,13] (choices 2) [3,17,18] profile15_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node44
  · exact profile15_node45
  · exact profile15_node46

def profile15_node47_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile15_node47 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,21] 3 profile15_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,21] 3 profile15_node47_cert).mp (by decide +kernel))

def profile15_node48_cert : CutBound 5 := { lost := (rows 0 4 24 16 0), upper := (rows 29 27 7 15 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile15_node48 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,25] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,25] 3 profile15_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,25] 3 profile15_node48_cert).mp (by decide +kernel))

def profile15_node50_cert : CutBound 5 := { lost := (rows 2 1 0 16 0), upper := (rows 29 30 7 15 23), lower := (rows 29 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 5 8 16) },{ target := 4, region := (rows 1 2 4 12 0), good := (rows 13 14 15 8 0) }] }

theorem profile15_node50 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28,3] 3 profile15_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28,3] 3 profile15_node50_cert).mp (by decide +kernel))

def profile15_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node49 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28] 3 (by decide) (choices 2) [3] profile15_node49_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28,28] (choices 2) [3] profile15_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node50

def profile15_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node42 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28] 3 (by decide) (choices 3) [13,21,25,28] profile15_node42_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [28] (choices 3) [13,21,25,28] profile15_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node43
  · exact profile15_node47
  · exact profile15_node48
  · exact profile15_node49

def profile15_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile15_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [] (choices 3) [14,22,26,28] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile15_node1
  · exact profile15_node18
  · exact profile15_node32
  · exact profile15_node42

theorem profile15 : Upper (D (n:=5) [50,50,35,34,18]) (R (n:=5) [50,50,35,34,18]) [] 3 := profile15_node0

def profile16_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 15 21 29 21), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile16_node2 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,13] 3 profile16_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,13] 3 profile16_node2_cert).mp (by decide +kernel))

def profile16_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 13 28 20), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile16_node4 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,9] 3 profile16_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,9] 3 profile16_node4_cert).mp (by decide +kernel))

def profile16_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 21 12 28), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile16_node5 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,17] 3 profile16_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,17] 3 profile16_node5_cert).mp (by decide +kernel))

def profile16_node6_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 23 28 13 21), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile16_node6 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,24] 3 profile16_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21,24] 3 profile16_node6_cert).mp (by decide +kernel))

def profile16_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node3 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21] 3 (by decide) (choices 2) [9,17,24] profile16_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,21] (choices 2) [9,17,24] profile16_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node4
  · exact profile16_node5
  · exact profile16_node6

def profile16_node7_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 30 21 29 21), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile16_node7 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,28] 3 profile16_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14,28] 3 profile16_node7_cert).mp (by decide +kernel))

def profile16_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node1 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14] 3 (by decide) (choices 3) [13,21,28] profile16_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [14] (choices 3) [13,21,28] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node2
  · exact profile16_node3
  · exact profile16_node7

def profile16_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 13 28 20), lower := (rows 23 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile16_node10 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,9] 3 profile16_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,9] 3 profile16_node10_cert).mp (by decide +kernel))

def profile16_node11_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 21 12 28), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile16_node11 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,17] 3 profile16_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,17] 3 profile16_node11_cert).mp (by decide +kernel))

def profile16_node12_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 15 28 13 21), lower := (rows 23 15 28 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile16_node12 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,24] 3 profile16_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13,24] 3 profile16_node12_cert).mp (by decide +kernel))

def profile16_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node9 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13] 3 (by decide) (choices 2) [9,17,24] profile16_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,13] (choices 2) [9,17,24] profile16_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node10
  · exact profile16_node11
  · exact profile16_node12

def profile16_node13_cert : CutBound 5 := { lost := (rows 8 8 0 0 0), upper := (rows 23 23 13 13 29), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node13 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,21] 3 profile16_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,21] 3 profile16_node13_cert).mp (by decide +kernel))

def profile16_node14_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 30 13 13 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node14 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,28] 3 profile16_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22,28] 3 profile16_node14_cert).mp (by decide +kernel))

def profile16_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node8 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22] 3 (by decide) (choices 3) [13,21,28] profile16_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [22] (choices 3) [13,21,28] profile16_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node9
  · exact profile16_node13
  · exact profile16_node14

def profile16_node16_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 15 23 31 23), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile16_node16 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,13] 3 profile16_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,13] 3 profile16_node16_cert).mp (by decide +kernel))

def profile16_node17_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node17 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,21] 3 profile16_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,21] 3 profile16_node17_cert).mp (by decide +kernel))

def profile16_node18_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 7 15 23), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile16_node18 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,28] 3 profile16_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28,28] 3 profile16_node18_cert).mp (by decide +kernel))

def profile16_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node15 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28] 3 (by decide) (choices 3) [13,21,28] profile16_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [28] (choices 3) [13,21,28] profile16_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node16
  · exact profile16_node17
  · exact profile16_node18

def profile16_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node0 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [] 3 (by decide) (choices 3) [14,22,28] profile16_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [] (choices 3) [14,22,28] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node1
  · exact profile16_node8
  · exact profile16_node15

theorem profile16 : Upper (D (n:=5) [50,49,36,34,18]) (R (n:=5) [50,49,36,34,18]) [] 3 := profile16_node0

def profile17_node2_cert : CutBound 5 := { lost := (rows 16 16 0 0 0), upper := (rows 15 15 29 29 29), lower := (rows 15 15 4 8 16), losses := [{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node2 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,13] 3 profile17_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,13] 3 profile17_node2_cert).mp (by decide +kernel))

def profile17_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 13 28 28), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile17_node4 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,9] 3 profile17_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,9] 3 profile17_node4_cert).mp (by decide +kernel))

def profile17_node5_cert : CutBound 5 := { lost := (rows 16 0 0 16 0), upper := (rows 15 23 28 13 29), lower := (rows 15 23 28 8 16), losses := [{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile17_node5 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,24] 3 profile17_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21,24] 3 profile17_node5_cert).mp (by decide +kernel))

def profile17_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node3 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21] 3 (by decide) (choices 2) [9,24] profile17_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,21] (choices 2) [9,24] profile17_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile17_node4
  · exact profile17_node5

def profile17_node6_cert : CutBound 5 := { lost := (rows 16 0 0 0 0), upper := (rows 15 30 29 29 29), lower := (rows 15 30 4 8 16), losses := [{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node6 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,28] 3 profile17_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14,28] 3 profile17_node6_cert).mp (by decide +kernel))

def profile17_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile17_node1 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14] 3 (by decide) (choices 3) [13,21,28] profile17_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [14] (choices 3) [13,21,28] profile17_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node2
  · exact profile17_node3
  · exact profile17_node6

def profile17_node9_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 13 28 28), lower := (rows 23 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile17_node9 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,9] 3 profile17_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,9] 3 profile17_node9_cert).mp (by decide +kernel))

def profile17_node10_cert : CutBound 5 := { lost := (rows 0 16 0 16 0), upper := (rows 23 15 28 13 29), lower := (rows 23 15 28 8 16), losses := [{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile17_node10 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,24] 3 profile17_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13,24] 3 profile17_node10_cert).mp (by decide +kernel))

def profile17_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node8 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13] 3 (by decide) (choices 2) [9,24] profile17_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,13] (choices 2) [9,24] profile17_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile17_node9
  · exact profile17_node10

def profile17_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 13 13 29), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node11 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,25] 3 profile17_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,25] 3 profile17_node11_cert).mp (by decide +kernel))

def profile17_node12_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 30 13 13 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile17_node12 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,28] 3 profile17_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22,28] 3 profile17_node12_cert).mp (by decide +kernel))

def profile17_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node7 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22] 3 (by decide) (choices 3) [13,25,28] profile17_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [22] (choices 3) [13,25,28] profile17_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node8
  · exact profile17_node11
  · exact profile17_node12

def profile17_node14_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 29 15 31 31 31), lower := (rows 29 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node14 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,13] 3 profile17_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,13] 3 profile17_node14_cert).mp (by decide +kernel))

def profile17_node15_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile17_node15 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,21] 3 profile17_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,21] 3 profile17_node15_cert).mp (by decide +kernel))

def profile17_node16_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 15 15 31), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile17_node16 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,28] 3 profile17_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28,28] 3 profile17_node16_cert).mp (by decide +kernel))

def profile17_node13_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile17_node13 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28] 3 (by decide) (choices 3) [13,21,28] profile17_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [28] (choices 3) [13,21,28] profile17_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node14
  · exact profile17_node15
  · exact profile17_node16

def profile17_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile17_node0 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [] 3 (by decide) (choices 3) [14,22,28] profile17_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [] (choices 3) [14,22,28] profile17_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node1
  · exact profile17_node7
  · exact profile17_node13

theorem profile17 : Upper (D (n:=5) [50,49,35,35,18]) (R (n:=5) [50,49,35,35,18]) [] 3 := profile17_node0

def profile18_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 23 27 19), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile18_node2 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,5] 3 profile18_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,5] 3 profile18_node2_cert).mp (by decide +kernel))

def profile18_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 23 31 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile18_node3 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,17] 3 profile18_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,17] 3 profile18_node3_cert).mp (by decide +kernel))

def profile18_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 23 27 19), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile18_node4 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,20] 3 profile18_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30,20] 3 profile18_node4_cert).mp (by decide +kernel))

def profile18_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node1 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30] 3 := by
  apply routed_branch (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30] 3 (by decide) (choices 2) [5,17,20] profile18_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [30] (choices 2) [5,17,20] profile18_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile18_node2
  · exact profile18_node3
  · exact profile18_node4

def profile18_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node0 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [] 3 (by decide) (choices 4) [30] profile18_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [] (choices 4) [30] profile18_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node1

theorem profile18 : Upper (D (n:=5) [67,34,34,33,19]) (R (n:=5) [67,34,34,33,19]) [] 3 := profile18_node0

def profile19_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 23 27 19), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile19_node2 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,5] 3 profile19_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,5] 3 profile19_node2_cert).mp (by decide +kernel))

def profile19_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 23 31 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile19_node3 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,17] 3 profile19_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,17] 3 profile19_node3_cert).mp (by decide +kernel))

def profile19_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 23 27 19), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile19_node4 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,20] 3 profile19_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30,20] 3 profile19_node4_cert).mp (by decide +kernel))

def profile19_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node1 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30] 3 (by decide) (choices 2) [5,17,20] profile19_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [30] (choices 2) [5,17,20] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile19_node2
  · exact profile19_node3
  · exact profile19_node4

def profile19_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [] 3 (by decide) (choices 4) [30] profile19_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [] (choices 4) [30] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=5) [66,35,34,33,19]) (R (n:=5) [66,35,34,33,19]) [] 3 := profile19_node0

def profile20_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile20_node2 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14,21] 3 profile20_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14,21] 3 profile20_node2_cert).mp (by decide +kernel))

def profile20_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node1 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14] 3 (by decide) (choices 3) [21] profile20_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [14] (choices 3) [21] profile20_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node2

def profile20_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile20_node4 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,13] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,13] 3 profile20_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,13] 3 profile20_node4_cert).mp (by decide +kernel))

def profile20_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile20_node5 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,21] 3 profile20_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,21] 3 profile20_node5_cert).mp (by decide +kernel))

def profile20_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 7 29 21), lower := (rows 23 27 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile20_node7 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,3] 3 profile20_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,3] 3 profile20_node7_cert).mp (by decide +kernel))

def profile20_node8_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 27 21 15 23), lower := (rows 23 27 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 21 29 21 8 16) }] }

theorem profile20_node8 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,17] 3 profile20_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,17] 3 profile20_node8_cert).mp (by decide +kernel))

def profile20_node9_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 22 13 21), lower := (rows 23 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) }] }

theorem profile20_node9 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,18] 3 profile20_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25,18] 3 profile20_node9_cert).mp (by decide +kernel))

def profile20_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node6 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25] 3 (by decide) (choices 2) [3,17,18] profile20_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,25] (choices 2) [3,17,18] profile20_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node7
  · exact profile20_node8
  · exact profile20_node9

def profile20_node10_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 23 27 19), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile20_node10 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,28] 3 profile20_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22,28] 3 profile20_node10_cert).mp (by decide +kernel))

def profile20_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node3 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile20_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [22] (choices 3) [13,21,25,28] profile20_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node4
  · exact profile20_node5
  · exact profile20_node6
  · exact profile20_node10

def profile20_node13_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 7 29 21), lower := (rows 27 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile20_node13 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,3] 3 profile20_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,3] 3 profile20_node13_cert).mp (by decide +kernel))

def profile20_node14_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 23 21 15 23), lower := (rows 27 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) }] }

theorem profile20_node14 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,17] 3 profile20_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,17] 3 profile20_node14_cert).mp (by decide +kernel))

def profile20_node15_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 22 13 21), lower := (rows 27 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile20_node15 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,18] 3 profile20_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21,18] 3 profile20_node15_cert).mp (by decide +kernel))

def profile20_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node12 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21] 3 (by decide) (choices 2) [3,17,18] profile20_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26,21] (choices 2) [3,17,18] profile20_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node13
  · exact profile20_node14
  · exact profile20_node15

def profile20_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node11 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26] 3 (by decide) (choices 3) [21] profile20_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [26] (choices 3) [21] profile20_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node12

def profile20_node17_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 23 27 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile20_node17 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28,21] 3 profile20_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28,21] 3 profile20_node17_cert).mp (by decide +kernel))

def profile20_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node16 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28] 3 (by decide) (choices 3) [21] profile20_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [28] (choices 3) [21] profile20_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node17

def profile20_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node0 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [] 3 (by decide) (choices 3) [14,22,26,28] profile20_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [] (choices 3) [14,22,26,28] profile20_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile20_node1
  · exact profile20_node3
  · exact profile20_node11
  · exact profile20_node16

theorem profile20 : Upper (D (n:=5) [51,50,34,33,19]) (R (n:=5) [51,50,34,33,19]) [] 3 := profile20_node0

def profile21_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 21 30 22), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile21_node3 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,17] 3 profile21_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,17] 3 profile21_node3_cert).mp (by decide +kernel))

def profile21_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 23 22 29 21), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile21_node4 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,18] 3 profile21_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21,18] 3 profile21_node4_cert).mp (by decide +kernel))

def profile21_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node2 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21] 3 (by decide) (choices 2) [17,18] profile21_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14,21] (choices 2) [17,18] profile21_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node3
  · exact profile21_node4

def profile21_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14] 3 (by decide) (choices 3) [21] profile21_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [14] (choices 3) [21] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node2

def profile21_node7_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 21 30 22), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile21_node7 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,17] 3 profile21_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,17] 3 profile21_node7_cert).mp (by decide +kernel))

def profile21_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 15 22 29 21), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) }] }

theorem profile21_node8 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,18] 3 profile21_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13,18] 3 profile21_node8_cert).mp (by decide +kernel))

def profile21_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node6 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13] 3 (by decide) (choices 2) [17,18] profile21_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,13] (choices 2) [17,18] profile21_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile21_node7
  · exact profile21_node8

def profile21_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 23 7 28 28), lower := (rows 23 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile21_node10 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,3] 3 profile21_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,3] 3 profile21_node10_cert).mp (by decide +kernel))

def profile21_node11_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 23 13 30 22), lower := (rows 23 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile21_node11 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,9] 3 profile21_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,9] 3 profile21_node11_cert).mp (by decide +kernel))

def profile21_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 23 14 29 21), lower := (rows 23 23 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile21_node12 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,10] 3 profile21_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,10] 3 profile21_node12_cert).mp (by decide +kernel))

def profile21_node13_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 23 21 14 30), lower := (rows 23 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile21_node13 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,17] 3 profile21_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,17] 3 profile21_node13_cert).mp (by decide +kernel))

def profile21_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 23 22 13 29), lower := (rows 23 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 22 22 8 16) }] }

theorem profile21_node14 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,18] 3 profile21_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,18] 3 profile21_node14_cert).mp (by decide +kernel))

def profile21_node15_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 23 28 15 23), lower := (rows 23 23 28 8 16), losses := [{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile21_node15 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,24] 3 profile21_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21,24] 3 profile21_node15_cert).mp (by decide +kernel))

def profile21_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node9 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile21_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,21] (choices 2) [3,9,10,17,18,24] profile21_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node10
  · exact profile21_node11
  · exact profile21_node12
  · exact profile21_node13
  · exact profile21_node14
  · exact profile21_node15

def profile21_node17_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 7 28 20), lower := (rows 23 27 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile21_node17 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,3] 3 profile21_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,3] 3 profile21_node17_cert).mp (by decide +kernel))

def profile21_node18_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 21 14 22), lower := (rows 23 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile21_node18 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,17] 3 profile21_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,17] 3 profile21_node18_cert).mp (by decide +kernel))

def profile21_node19_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 22 13 21), lower := (rows 23 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) }] }

theorem profile21_node19 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,18] 3 profile21_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25,18] 3 profile21_node19_cert).mp (by decide +kernel))

def profile21_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node16 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25] 3 (by decide) (choices 2) [3,17,18] profile21_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,25] (choices 2) [3,17,18] profile21_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node17
  · exact profile21_node18
  · exact profile21_node19

def profile21_node21_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 30 7 29 21), lower := (rows 23 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) }] }

theorem profile21_node21 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,3] 3 profile21_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,3] 3 profile21_node21_cert).mp (by decide +kernel))

def profile21_node22_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 30 21 15 23), lower := (rows 23 30 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 28 21 8 16) }] }

theorem profile21_node22 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,17] 3 profile21_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,17] 3 profile21_node22_cert).mp (by decide +kernel))

def profile21_node23_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 30 22 13 21), lower := (rows 23 30 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) }] }

theorem profile21_node23 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,18] 3 profile21_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28,18] 3 profile21_node23_cert).mp (by decide +kernel))

def profile21_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node20 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28] 3 (by decide) (choices 2) [3,17,18] profile21_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22,28] (choices 2) [3,17,18] profile21_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node21
  · exact profile21_node22
  · exact profile21_node23

def profile21_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node5 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile21_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [22] (choices 3) [13,21,25,28] profile21_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node6
  · exact profile21_node9
  · exact profile21_node16
  · exact profile21_node20

def profile21_node26_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 7 28 20), lower := (rows 27 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) }] }

theorem profile21_node26 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,3] 3 profile21_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,3] 3 profile21_node26_cert).mp (by decide +kernel))

def profile21_node27_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 21 14 22), lower := (rows 27 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) }] }

theorem profile21_node27 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,17] 3 profile21_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,17] 3 profile21_node27_cert).mp (by decide +kernel))

def profile21_node28_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 22 13 21), lower := (rows 27 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile21_node28 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,18] 3 profile21_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21,18] 3 profile21_node28_cert).mp (by decide +kernel))

def profile21_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node25 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21] 3 (by decide) (choices 2) [3,17,18] profile21_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26,21] (choices 2) [3,17,18] profile21_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node26
  · exact profile21_node27
  · exact profile21_node28

def profile21_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node24 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26] 3 (by decide) (choices 3) [21] profile21_node24_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [26] (choices 3) [21] profile21_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node25

def profile21_node31_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 23 7 30 22), lower := (rows 29 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) }] }

theorem profile21_node31 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,3] 3 profile21_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,3] 3 profile21_node31_cert).mp (by decide +kernel))

def profile21_node32_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 23 21 14 22), lower := (rows 29 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) }] }

theorem profile21_node32 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,17] 3 profile21_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,17] 3 profile21_node32_cert).mp (by decide +kernel))

def profile21_node33_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 29 23 22 15 23), lower := (rows 29 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 22 22 8 16) }] }

theorem profile21_node33 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,18] 3 profile21_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21,18] 3 profile21_node33_cert).mp (by decide +kernel))

def profile21_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node30 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21] 3 (by decide) (choices 2) [3,17,18] profile21_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28,21] (choices 2) [3,17,18] profile21_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node31
  · exact profile21_node32
  · exact profile21_node33

def profile21_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node29 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28] 3 (by decide) (choices 3) [21] profile21_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [28] (choices 3) [21] profile21_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node30

def profile21_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [] 3 (by decide) (choices 3) [14,22,26,28] profile21_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [] (choices 3) [14,22,26,28] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node1
  · exact profile21_node5
  · exact profile21_node24
  · exact profile21_node29

theorem profile21 : Upper (D (n:=5) [50,50,35,33,19]) (R (n:=5) [50,50,35,33,19]) [] 3 := profile21_node0

def profile22_node2_cert : CutBound 5 := { lost := (rows 0 24 0 4 0), upper := (rows 31 7 31 27 27), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile22_node2 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,5] 3 profile22_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,5] 3 profile22_node2_cert).mp (by decide +kernel))

def profile22_node3_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile22_node3 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,12] 3 profile22_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,12] 3 profile22_node3_cert).mp (by decide +kernel))

def profile22_node5_cert : CutBound 5 := { lost := (rows 0 4 0 3 0), upper := (rows 31 19 7 28 28), lower := (rows 31 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 3 8 16) }] }

theorem profile22_node5 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,3] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,3] 3 profile22_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,3] 3 profile22_node5_cert).mp (by decide +kernel))

def profile22_node6_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 31 19 13 30 22), lower := (rows 31 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 11 8 16) }] }

theorem profile22_node6 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,9] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,9] 3 profile22_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,9] 3 profile22_node6_cert).mp (by decide +kernel))

def profile22_node7_cert : CutBound 5 := { lost := (rows 0 4 1 2 0), upper := (rows 31 19 14 29 21), lower := (rows 31 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 10 8 16) }] }

theorem profile22_node7 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,10] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,10] 3 profile22_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,10] 3 profile22_node7_cert).mp (by decide +kernel))

def profile22_node8_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 31 19 21 14 30), lower := (rows 31 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 19 19 8 16) }] }

theorem profile22_node8 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,17] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,17] 3 profile22_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,17] 3 profile22_node8_cert).mp (by decide +kernel))

def profile22_node9_cert : CutBound 5 := { lost := (rows 0 4 1 2 0), upper := (rows 31 19 22 13 29), lower := (rows 31 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 18 8 16) }] }

theorem profile22_node9 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,18] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,18] 3 profile22_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,18] 3 profile22_node9_cert).mp (by decide +kernel))

def profile22_node10_cert : CutBound 5 := { lost := (rows 0 4 3 0 0), upper := (rows 31 19 28 15 23), lower := (rows 31 19 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 28 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 24 8 16) }] }

theorem profile22_node10 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,24] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,24] 3 profile22_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17,24] 3 profile22_node10_cert).mp (by decide +kernel))

def profile22_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node4 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile22_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,17] (choices 2) [3,9,10,17,18,24] profile22_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node5
  · exact profile22_node6
  · exact profile22_node7
  · exact profile22_node8
  · exact profile22_node9
  · exact profile22_node10

def profile22_node11_cert : CutBound 5 := { lost := (rows 0 9 0 4 0), upper := (rows 31 22 31 27 27), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 22 4 0 16) }] }

theorem profile22_node11 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,20] 3 profile22_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30,20] 3 profile22_node11_cert).mp (by decide +kernel))

def profile22_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile22_node1 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30] 3 (by decide) (choices 2) [5,12,17,20] profile22_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [30] (choices 2) [5,12,17,20] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node2
  · exact profile22_node3
  · exact profile22_node4
  · exact profile22_node11

def profile22_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [] 3 (by decide) (choices 4) [30] profile22_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [] (choices 4) [30] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=5) [66,34,34,34,19]) (R (n:=5) [66,34,34,34,19]) [] 3 := profile22_node0

def profile23_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 30 26 26), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile23_node2 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,5] 3 profile23_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,5] 3 profile23_node2_cert).mp (by decide +kernel))

def profile23_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile23_node3 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,12] 3 profile23_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,12] 3 profile23_node3_cert).mp (by decide +kernel))

def profile23_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 30 30 30), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile23_node4 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,17] 3 profile23_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,17] 3 profile23_node4_cert).mp (by decide +kernel))

def profile23_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 22 31 27 27), lower := (rows 31 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile23_node5 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,20] 3 profile23_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30,20] 3 profile23_node5_cert).mp (by decide +kernel))

def profile23_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile23_node1 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30] 3 := by
  apply routed_branch (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30] 3 (by decide) (choices 2) [5,12,17,20] profile23_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [30] (choices 2) [5,12,17,20] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile23_node2
  · exact profile23_node3
  · exact profile23_node4
  · exact profile23_node5

def profile23_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [] 3 (by decide) (choices 4) [30] profile23_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [] (choices 4) [30] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=5) [65,35,34,34,19]) (R (n:=5) [65,35,34,34,19]) [] 3 := profile23_node0

#print axioms profile23
end Delivery.FiveVertexPositive11
