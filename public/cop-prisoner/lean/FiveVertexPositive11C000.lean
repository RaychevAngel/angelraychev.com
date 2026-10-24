import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 23 27 19), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,5] 3 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,5] 3 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 7 15 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile0_node3 : Upper (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,17] 3 profile0_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30,17] 3 profile0_node3_cert).mp (by decide +kernel))

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30] 3 (by decide) (choices 2) [5,17] profile0_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [30] (choices 2) [5,17] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node2
  · exact profile0_node3

def profile0_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [] 3 (by decide) (choices 4) [30] profile0_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [] (choices 4) [30] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=5) [68,34,34,33,18]) (R (n:=5) [68,34,34,33,18]) [] 3 := profile0_node0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 23 27 19), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile1_node2 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,5] 3 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,5] 3 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 7 15 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile1_node3 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,17] 3 profile1_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,17] 3 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 7 11 19), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile1_node4 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,20] 3 profile1_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30,20] 3 profile1_node4_cert).mp (by decide +kernel))

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30] 3 (by decide) (choices 2) [5,17,20] profile1_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [30] (choices 2) [5,17,20] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4

def profile1_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [] 3 (by decide) (choices 4) [30] profile1_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [] (choices 4) [30] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=5) [67,35,34,33,18]) (R (n:=5) [67,35,34,33,18]) [] 3 := profile1_node0

def profile2_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 23 27 19), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile2_node2 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,5] 3 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,5] 3 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 7 15 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile2_node3 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,17] 3 profile2_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,17] 3 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 7 11 19), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile2_node4 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,20] 3 profile2_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30,20] 3 profile2_node4_cert).mp (by decide +kernel))

def profile2_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30] 3 (by decide) (choices 2) [5,17,20] profile2_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [30] (choices 2) [5,17,20] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4

def profile2_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [] 3 (by decide) (choices 4) [30] profile2_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [] (choices 4) [30] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [66,36,34,33,18]) (R (n:=5) [66,36,34,33,18]) [] 3 := profile2_node0

def profile3_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile3_node2 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14,21] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14,21] 3 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14,21] 3 profile3_node2_cert).mp (by decide +kernel))

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14] 3 (by decide) (choices 3) [21] profile3_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [14] (choices 3) [21] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile3_node4 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,13] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,13] 3 profile3_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,13] 3 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 15 11 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile3_node5 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,21] 3 profile3_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,21] 3 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 7 15 23), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile3_node6 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,25] 3 profile3_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22,25] 3 profile3_node6_cert).mp (by decide +kernel))

def profile3_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22] 3 (by decide) (choices 3) [13,21,25] profile3_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [22] (choices 3) [13,21,25] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6

def profile3_node8_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 7 15 23), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile3_node8 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26,21] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26,21] 3 profile3_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26,21] 3 profile3_node8_cert).mp (by decide +kernel))

def profile3_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node7 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26] 3 (by decide) (choices 3) [21] profile3_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [26] (choices 3) [21] profile3_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node8

def profile3_node10_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 7 11 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile3_node10 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28,21] 3 profile3_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28,21] 3 profile3_node10_cert).mp (by decide +kernel))

def profile3_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node9 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28] 3 (by decide) (choices 3) [21] profile3_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [28] (choices 3) [21] profile3_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node10

def profile3_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile3_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [] (choices 3) [14,22,26,28] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node3
  · exact profile3_node7
  · exact profile3_node9

theorem profile3 : Upper (D (n:=5) [52,50,34,33,18]) (R (n:=5) [52,50,34,33,18]) [] 3 := profile3_node0

def profile4_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile4_node2 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14,21] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14,21] 3 profile4_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14,21] 3 profile4_node2_cert).mp (by decide +kernel))

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14] 3 (by decide) (choices 3) [21] profile4_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [14] (choices 3) [21] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node2

def profile4_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile4_node4 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,13] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,13] 3 profile4_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,13] 3 profile4_node4_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 15 11 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile4_node5 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,21] 3 profile4_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,21] 3 profile4_node5_cert).mp (by decide +kernel))

def profile4_node6_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 7 15 23), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile4_node6 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,25] 3 profile4_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,25] 3 profile4_node6_cert).mp (by decide +kernel))

def profile4_node7_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 7 11 19), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile4_node7 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,28] 3 profile4_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22,28] 3 profile4_node7_cert).mp (by decide +kernel))

def profile4_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile4_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [22] (choices 3) [13,21,25,28] profile4_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node4
  · exact profile4_node5
  · exact profile4_node6
  · exact profile4_node7

def profile4_node9_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 7 15 23), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile4_node9 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26,21] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26,21] 3 profile4_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26,21] 3 profile4_node9_cert).mp (by decide +kernel))

def profile4_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node8 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26] 3 (by decide) (choices 3) [21] profile4_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [26] (choices 3) [21] profile4_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node9

def profile4_node11_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 7 11 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile4_node11 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28,21] 3 profile4_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28,21] 3 profile4_node11_cert).mp (by decide +kernel))

def profile4_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node10 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28] 3 (by decide) (choices 3) [21] profile4_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [28] (choices 3) [21] profile4_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node11

def profile4_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile4_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [] (choices 3) [14,22,26,28] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node3
  · exact profile4_node8
  · exact profile4_node10

theorem profile4 : Upper (D (n:=5) [51,51,34,33,18]) (R (n:=5) [51,51,34,33,18]) [] 3 := profile4_node0

def profile5_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 7 23 31 23), lower := (rows 31 7 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile5_node2 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,5] 3 profile5_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,5] 3 profile5_node2_cert).mp (by decide +kernel))

def profile5_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 7 15 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile5_node3 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,17] 3 profile5_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,17] 3 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 7 15 23), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile5_node4 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,20] 3 profile5_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30,20] 3 profile5_node4_cert).mp (by decide +kernel))

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30] 3 (by decide) (choices 2) [5,17,20] profile5_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [30] (choices 2) [5,17,20] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node4

def profile5_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [] 3 (by decide) (choices 4) [30] profile5_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [] (choices 4) [30] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node1

theorem profile5 : Upper (D (n:=5) [66,35,35,33,18]) (R (n:=5) [66,35,35,33,18]) [] 3 := profile5_node0

def profile6_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 23 7 29 21), lower := (rows 15 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile6_node3 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,3] 3 profile6_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,3] 3 profile6_node3_cert).mp (by decide +kernel))

def profile6_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 23 21 15 23), lower := (rows 15 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile6_node4 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,17] 3 profile6_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,17] 3 profile6_node4_cert).mp (by decide +kernel))

def profile6_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 23 22 13 21), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile6_node5 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,18] 3 profile6_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21,18] 3 profile6_node5_cert).mp (by decide +kernel))

def profile6_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node2 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21] 3 (by decide) (choices 2) [3,17,18] profile6_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14,21] (choices 2) [3,17,18] profile6_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node3
  · exact profile6_node4
  · exact profile6_node5

def profile6_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node1 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14] 3 (by decide) (choices 3) [21] profile6_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [14] (choices 3) [21] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node2

def profile6_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 15 7 29 21), lower := (rows 23 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile6_node8 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,3] 3 profile6_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,3] 3 profile6_node8_cert).mp (by decide +kernel))

def profile6_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 15 21 15 23), lower := (rows 23 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) }] }

theorem profile6_node9 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,17] 3 profile6_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,17] 3 profile6_node9_cert).mp (by decide +kernel))

def profile6_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 15 22 13 21), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) }] }

theorem profile6_node10 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,18] 3 profile6_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13,18] 3 profile6_node10_cert).mp (by decide +kernel))

def profile6_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node7 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13] 3 (by decide) (choices 2) [3,17,18] profile6_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,13] (choices 2) [3,17,18] profile6_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node10

def profile6_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node11 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,21] 3 profile6_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,21] 3 profile6_node11_cert).mp (by decide +kernel))

def profile6_node12_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 7 15 23), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node12 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,25] 3 profile6_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,25] 3 profile6_node12_cert).mp (by decide +kernel))

def profile6_node13_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 30 7 15 23), lower := (rows 23 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile6_node13 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,28] 3 profile6_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22,28] 3 profile6_node13_cert).mp (by decide +kernel))

def profile6_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node6 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile6_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [22] (choices 3) [13,21,25,28] profile6_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node7
  · exact profile6_node11
  · exact profile6_node12
  · exact profile6_node13

def profile6_node15_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 7 15 23), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node15 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26,21] 3 profile6_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26,21] 3 profile6_node15_cert).mp (by decide +kernel))

def profile6_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node14 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26] 3 (by decide) (choices 3) [21] profile6_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [26] (choices 3) [21] profile6_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node15

def profile6_node17_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 23 7 15 23), lower := (rows 29 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile6_node17 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28,21] 3 profile6_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28,21] 3 profile6_node17_cert).mp (by decide +kernel))

def profile6_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node16 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28] 3 (by decide) (choices 3) [21] profile6_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [28] (choices 3) [21] profile6_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node17

def profile6_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile6_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [] (choices 3) [14,22,26,28] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node1
  · exact profile6_node6
  · exact profile6_node14
  · exact profile6_node16

theorem profile6 : Upper (D (n:=5) [51,50,35,33,18]) (R (n:=5) [51,50,35,33,18]) [] 3 := profile6_node0

def profile7_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 7 28 20), lower := (rows 15 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile7_node3 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,3] 3 profile7_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,3] 3 profile7_node3_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 21 14 22), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile7_node4 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,17] 3 profile7_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,17] 3 profile7_node4_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 23 22 13 21), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile7_node5 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,18] 3 profile7_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21,18] 3 profile7_node5_cert).mp (by decide +kernel))

def profile7_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node2 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21] 3 (by decide) (choices 2) [3,17,18] profile7_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14,21] (choices 2) [3,17,18] profile7_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node3
  · exact profile7_node4
  · exact profile7_node5

def profile7_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14] 3 (by decide) (choices 3) [21] profile7_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [14] (choices 3) [21] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node2

def profile7_node8_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 7 28 20), lower := (rows 23 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile7_node8 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,3] 3 profile7_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,3] 3 profile7_node8_cert).mp (by decide +kernel))

def profile7_node9_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 21 14 22), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile7_node9 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,17] 3 profile7_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,17] 3 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 15 22 13 21), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) }] }

theorem profile7_node10 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,18] 3 profile7_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13,18] 3 profile7_node10_cert).mp (by decide +kernel))

def profile7_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node7 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13] 3 (by decide) (choices 2) [3,17,18] profile7_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,13] (choices 2) [3,17,18] profile7_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node8
  · exact profile7_node9
  · exact profile7_node10

def profile7_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile7_node11 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,21] 3 profile7_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,21] 3 profile7_node11_cert).mp (by decide +kernel))

def profile7_node12_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 30 7 15 23), lower := (rows 23 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile7_node12 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,28] 3 profile7_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22,28] 3 profile7_node12_cert).mp (by decide +kernel))

def profile7_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node6 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22] 3 (by decide) (choices 3) [13,21,28] profile7_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [22] (choices 3) [13,21,28] profile7_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node7
  · exact profile7_node11
  · exact profile7_node12

def profile7_node14_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 23 7 15 23), lower := (rows 29 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile7_node14 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28,21] 3 profile7_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28,21] 3 profile7_node14_cert).mp (by decide +kernel))

def profile7_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node13 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28] 3 (by decide) (choices 3) [21] profile7_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [28] (choices 3) [21] profile7_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node14

def profile7_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [] 3 (by decide) (choices 3) [14,22,28] profile7_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [] (choices 3) [14,22,28] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node1
  · exact profile7_node6
  · exact profile7_node13

theorem profile7 : Upper (D (n:=5) [50,50,36,33,18]) (R (n:=5) [50,50,36,33,18]) [] 3 := profile7_node0

def profile8_node2_cert : CutBound 5 := { lost := (rows 0 24 0 4 0), upper := (rows 31 7 31 27 27), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile8_node2 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,5] 3 profile8_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,5] 3 profile8_node2_cert).mp (by decide +kernel))

def profile8_node3_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile8_node3 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,12] 3 profile8_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,12] 3 profile8_node3_cert).mp (by decide +kernel))

def profile8_node4_cert : CutBound 5 := { lost := (rows 0 12 16 16 0), upper := (rows 31 19 15 15 31), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile8_node4 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,17] 3 profile8_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,17] 3 profile8_node4_cert).mp (by decide +kernel))

def profile8_node5_cert : CutBound 5 := { lost := (rows 0 9 0 4 0), upper := (rows 31 22 15 11 27), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 22 4 0 16) }] }

theorem profile8_node5 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,20] 3 profile8_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30,20] 3 profile8_node5_cert).mp (by decide +kernel))

def profile8_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile8_node1 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30] 3 (by decide) (choices 2) [5,12,17,20] profile8_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [30] (choices 2) [5,12,17,20] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node2
  · exact profile8_node3
  · exact profile8_node4
  · exact profile8_node5

def profile8_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [] 3 (by decide) (choices 4) [30] profile8_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [] (choices 4) [30] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node1

theorem profile8 : Upper (D (n:=5) [67,34,34,34,18]) (R (n:=5) [67,34,34,34,18]) [] 3 := profile8_node0

def profile9_node2_cert : CutBound 5 := { lost := (rows 0 24 0 4 0), upper := (rows 31 7 31 27 27), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile9_node2 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,5] 3 profile9_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,5] 3 profile9_node2_cert).mp (by decide +kernel))

def profile9_node3_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile9_node3 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,12] 3 profile9_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,12] 3 profile9_node3_cert).mp (by decide +kernel))

def profile9_node4_cert : CutBound 5 := { lost := (rows 0 12 16 16 0), upper := (rows 31 19 15 15 31), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile9_node4 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,17] 3 profile9_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,17] 3 profile9_node4_cert).mp (by decide +kernel))

def profile9_node5_cert : CutBound 5 := { lost := (rows 0 9 0 4 0), upper := (rows 31 22 15 11 27), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 22 4 0 16) }] }

theorem profile9_node5 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,20] 3 profile9_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30,20] 3 profile9_node5_cert).mp (by decide +kernel))

def profile9_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile9_node1 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30] 3 (by decide) (choices 2) [5,12,17,20] profile9_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [30] (choices 2) [5,12,17,20] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node2
  · exact profile9_node3
  · exact profile9_node4
  · exact profile9_node5

def profile9_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [] 3 (by decide) (choices 4) [30] profile9_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [] (choices 4) [30] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=5) [66,35,34,34,18]) (R (n:=5) [66,35,34,34,18]) [] 3 := profile9_node0

def profile10_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 7 30 26 26), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile10_node2 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,5] 3 profile10_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,5] 3 profile10_node2_cert).mp (by decide +kernel))

def profile10_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile10_node3 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,12] 3 profile10_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,12] 3 profile10_node3_cert).mp (by decide +kernel))

def profile10_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 14 14 30), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile10_node4 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,17] 3 profile10_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,17] 3 profile10_node4_cert).mp (by decide +kernel))

def profile10_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 22 15 11 27), lower := (rows 31 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile10_node5 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,20] 3 profile10_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30,20] 3 profile10_node5_cert).mp (by decide +kernel))

def profile10_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile10_node1 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30] 3 (by decide) (choices 2) [5,12,17,20] profile10_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [30] (choices 2) [5,12,17,20] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile10_node2
  · exact profile10_node3
  · exact profile10_node4
  · exact profile10_node5

def profile10_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [] 3 (by decide) (choices 4) [30] profile10_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [] (choices 4) [30] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=5) [65,36,34,34,18]) (R (n:=5) [65,36,34,34,18]) [] 3 := profile10_node0

def profile11_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 15 21 25 17), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile11_node2 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,13] 3 profile11_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,13] 3 profile11_node2_cert).mp (by decide +kernel))

def profile11_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 29 25 25), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile11_node3 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,21] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,21] 3 profile11_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14,21] 3 profile11_node3_cert).mp (by decide +kernel))

def profile11_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile11_node1 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14] 3 (by decide) (choices 3) [13,21] profile11_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [14] (choices 3) [13,21] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node2
  · exact profile11_node3

def profile11_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 29 25 25), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile11_node5 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,13] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,13] 3 profile11_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,13] 3 profile11_node5_cert).mp (by decide +kernel))

def profile11_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 13 9 25), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile11_node6 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,21] 3 profile11_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,21] 3 profile11_node6_cert).mp (by decide +kernel))

def profile11_node7_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 13 13 29), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile11_node7 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,25] 3 profile11_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22,25] 3 profile11_node7_cert).mp (by decide +kernel))

def profile11_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node4 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22] 3 (by decide) (choices 3) [13,21,25] profile11_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [22] (choices 3) [13,21,25] profile11_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node5
  · exact profile11_node6
  · exact profile11_node7

def profile11_node9_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile11_node9 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,13] 3 profile11_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,13] 3 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 15 11 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile11_node10 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,21] 3 profile11_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28,21] 3 profile11_node10_cert).mp (by decide +kernel))

def profile11_node8_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile11_node8 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28] 3 (by decide) (choices 3) [13,21] profile11_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [28] (choices 3) [13,21] profile11_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node9
  · exact profile11_node10

def profile11_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile11_node0 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [] 3 (by decide) (choices 3) [14,22,28] profile11_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [] (choices 3) [14,22,28] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node1
  · exact profile11_node4
  · exact profile11_node8

theorem profile11 : Upper (D (n:=5) [52,49,34,34,18]) (R (n:=5) [52,49,34,34,18]) [] 3 := profile11_node0

def profile12_node2_cert : CutBound 5 := { lost := (rows 16 16 8 4 0), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile12_node2 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,13] 3 profile12_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,13] 3 profile12_node2_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 5 := { lost := (rows 0 0 8 6 0), upper := (rows 15 23 7 25 25), lower := (rows 15 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile12_node4 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,3] 3 profile12_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,3] 3 profile12_node4_cert).mp (by decide +kernel))

def profile12_node5_cert : CutBound 5 := { lost := (rows 0 8 2 4 0), upper := (rows 15 23 13 27 19), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile12_node5 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,9] 3 profile12_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,9] 3 profile12_node5_cert).mp (by decide +kernel))

def profile12_node6_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 15 23 14 25 17), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile12_node6 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,10] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,10] 3 profile12_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,10] 3 profile12_node6_cert).mp (by decide +kernel))

def profile12_node7_cert : CutBound 5 := { lost := (rows 0 8 10 4 0), upper := (rows 15 23 21 11 27), lower := (rows 15 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile12_node7 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,17] 3 profile12_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,17] 3 profile12_node7_cert).mp (by decide +kernel))

def profile12_node8_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 15 23 22 9 25), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile12_node8 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,18] 3 profile12_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,18] 3 profile12_node8_cert).mp (by decide +kernel))

def profile12_node9_cert : CutBound 5 := { lost := (rows 16 8 0 20 0), upper := (rows 15 23 28 11 19), lower := (rows 15 23 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile12_node9 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,24] 3 profile12_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21,24] 3 profile12_node9_cert).mp (by decide +kernel))

def profile12_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node3 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile12_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,21] (choices 2) [3,9,10,17,18,24] profile12_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node4
  · exact profile12_node5
  · exact profile12_node6
  · exact profile12_node7
  · exact profile12_node8
  · exact profile12_node9

def profile12_node10_cert : CutBound 5 := { lost := (rows 16 0 8 4 0), upper := (rows 15 30 23 27 19), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile12_node10 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,28] 3 profile12_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14,28] 3 profile12_node10_cert).mp (by decide +kernel))

def profile12_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile12_node1 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14] 3 (by decide) (choices 3) [13,21,28] profile12_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [14] (choices 3) [13,21,28] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node10

def profile12_node13_cert : CutBound 5 := { lost := (rows 0 0 8 6 0), upper := (rows 23 15 7 25 25), lower := (rows 23 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile12_node13 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,3] 3 profile12_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,3] 3 profile12_node13_cert).mp (by decide +kernel))

def profile12_node14_cert : CutBound 5 := { lost := (rows 8 0 2 4 0), upper := (rows 23 15 13 27 19), lower := (rows 23 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile12_node14 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,9] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,9] 3 profile12_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,9] 3 profile12_node14_cert).mp (by decide +kernel))

def profile12_node15_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 23 15 14 25 17), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile12_node15 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,10] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,10] 3 profile12_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,10] 3 profile12_node15_cert).mp (by decide +kernel))

def profile12_node16_cert : CutBound 5 := { lost := (rows 0 0 10 4 0), upper := (rows 23 15 21 11 27), lower := (rows 23 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) }] }

theorem profile12_node16 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,17] 3 profile12_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,17] 3 profile12_node16_cert).mp (by decide +kernel))

def profile12_node17_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 23 15 22 9 25), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile12_node17 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,18] 3 profile12_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,18] 3 profile12_node17_cert).mp (by decide +kernel))

def profile12_node18_cert : CutBound 5 := { lost := (rows 8 16 0 20 0), upper := (rows 23 15 28 11 19), lower := (rows 23 15 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile12_node18 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,24] 3 profile12_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13,24] 3 profile12_node18_cert).mp (by decide +kernel))

def profile12_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node12 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile12_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,13] (choices 2) [3,9,10,17,18,24] profile12_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node13
  · exact profile12_node14
  · exact profile12_node15
  · exact profile12_node16
  · exact profile12_node17
  · exact profile12_node18

def profile12_node19_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 15 11 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile12_node19 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,21] 3 profile12_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,21] 3 profile12_node19_cert).mp (by decide +kernel))

def profile12_node21_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 27 7 13 29), lower := (rows 23 27 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile12_node21 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,3] 3 profile12_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,3] 3 profile12_node21_cert).mp (by decide +kernel))

def profile12_node22_cert : CutBound 5 := { lost := (rows 0 0 18 16 0), upper := (rows 23 27 13 15 23), lower := (rows 23 27 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 13 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile12_node22 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,9] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,9] 3 profile12_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,9] 3 profile12_node22_cert).mp (by decide +kernel))

def profile12_node23_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 14 13 21), lower := (rows 23 27 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile12_node23 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,10] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,10] 3 profile12_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25,10] 3 profile12_node23_cert).mp (by decide +kernel))

def profile12_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node20 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25] 3 (by decide) (choices 2) [3,9,10] profile12_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,25] (choices 2) [3,9,10] profile12_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node21
  · exact profile12_node22
  · exact profile12_node23

def profile12_node24_cert : CutBound 5 := { lost := (rows 8 0 16 20 0), upper := (rows 23 30 15 11 27), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile12_node24 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,28] 3 profile12_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22,28] 3 profile12_node24_cert).mp (by decide +kernel))

def profile12_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node11 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile12_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [22] (choices 3) [13,21,25,28] profile12_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node12
  · exact profile12_node19
  · exact profile12_node20
  · exact profile12_node24

def profile12_node26_cert : CutBound 5 := { lost := (rows 0 16 8 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile12_node26 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,13] 3 profile12_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,13] 3 profile12_node26_cert).mp (by decide +kernel))

def profile12_node27_cert : CutBound 5 := { lost := (rows 0 8 16 20 0), upper := (rows 29 23 15 11 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile12_node27 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,21] 3 profile12_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,21] 3 profile12_node27_cert).mp (by decide +kernel))

def profile12_node29_cert : CutBound 5 := { lost := (rows 2 1 0 4 0), upper := (rows 29 30 7 11 19), lower := (rows 29 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 5 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile12_node29 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28,3] 3 :=
  cut_bound_sound (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28,3] 3 profile12_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28,3] 3 profile12_node29_cert).mp (by decide +kernel))

def profile12_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node28 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28] 3 (by decide) (choices 2) [3] profile12_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28,28] (choices 2) [3] profile12_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node29

def profile12_node25_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile12_node25 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28] 3 (by decide) (choices 3) [13,21,28] profile12_node25_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [28] (choices 3) [13,21,28] profile12_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node26
  · exact profile12_node27
  · exact profile12_node28

def profile12_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile12_node0 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [] 3 (by decide) (choices 3) [14,22,28] profile12_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [] (choices 3) [14,22,28] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node1
  · exact profile12_node11
  · exact profile12_node25

theorem profile12 : Upper (D (n:=5) [51,50,34,34,18]) (R (n:=5) [51,50,34,34,18]) [] 3 := profile12_node0

def profile13_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 7 30 30 30), lower := (rows 31 7 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile13_node2 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,5] 3 profile13_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,5] 3 profile13_node2_cert).mp (by decide +kernel))

def profile13_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 11 22 30 22), lower := (rows 31 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) }] }

theorem profile13_node3 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,9] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,9] 3 profile13_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,9] 3 profile13_node3_cert).mp (by decide +kernel))

def profile13_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 14 23 31 23), lower := (rows 31 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile13_node4 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,12] 3 profile13_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,12] 3 profile13_node4_cert).mp (by decide +kernel))

def profile13_node5_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 14 14 30), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile13_node5 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,17] 3 profile13_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,17] 3 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 22 15 15 31), lower := (rows 31 22 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 22 4 0 16) }] }

theorem profile13_node6 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,20] 3 profile13_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,20] 3 profile13_node6_cert).mp (by decide +kernel))

def profile13_node7_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 26 7 15 23), lower := (rows 31 26 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 26 0 8 16) }] }

theorem profile13_node7 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,24] 3 :=
  cut_bound_sound (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,24] 3 profile13_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30,24] 3 profile13_node7_cert).mp (by decide +kernel))

def profile13_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node1 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile13_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [30] (choices 2) [5,9,12,17,20,24] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node3
  · exact profile13_node4
  · exact profile13_node5
  · exact profile13_node6
  · exact profile13_node7

def profile13_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [] 3 (by decide) (choices 4) [30] profile13_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [] (choices 4) [30] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=5) [65,35,35,34,18]) (R (n:=5) [65,35,35,34,18]) [] 3 := profile13_node0

def profile14_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 15 21 29 21), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile14_node2 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,13] 3 profile14_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,13] 3 profile14_node2_cert).mp (by decide +kernel))

def profile14_node4_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 23 13 29 21), lower := (rows 15 23 13 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile14_node4 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,9] 3 profile14_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,9] 3 profile14_node4_cert).mp (by decide +kernel))

def profile14_node5_cert : CutBound 5 := { lost := (rows 0 8 8 0 0), upper := (rows 15 23 21 13 29), lower := (rows 15 23 21 8 16), losses := [{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile14_node5 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,17] 3 profile14_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,17] 3 profile14_node5_cert).mp (by decide +kernel))

def profile14_node6_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 23 28 13 21), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile14_node6 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,24] 3 profile14_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21,24] 3 profile14_node6_cert).mp (by decide +kernel))

def profile14_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node3 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21] 3 (by decide) (choices 2) [9,17,24] profile14_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,21] (choices 2) [9,17,24] profile14_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node4
  · exact profile14_node5
  · exact profile14_node6

def profile14_node7_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 21 29 21), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile14_node7 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,25] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,25] 3 profile14_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,25] 3 profile14_node7_cert).mp (by decide +kernel))

def profile14_node8_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 30 21 29 21), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile14_node8 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,28] 3 profile14_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14,28] 3 profile14_node8_cert).mp (by decide +kernel))

def profile14_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14] 3 (by decide) (choices 3) [13,21,25,28] profile14_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [14] (choices 3) [13,21,25,28] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node3
  · exact profile14_node7
  · exact profile14_node8

def profile14_node11_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 15 13 29 21), lower := (rows 23 15 13 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 23), good := (rows 23 23 21 0 16) }] }

theorem profile14_node11 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,9] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,9] 3 profile14_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,9] 3 profile14_node11_cert).mp (by decide +kernel))

def profile14_node12_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 23 15 21 13 29), lower := (rows 23 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) }] }

theorem profile14_node12 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,17] 3 profile14_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,17] 3 profile14_node12_cert).mp (by decide +kernel))

def profile14_node13_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 15 28 13 21), lower := (rows 23 15 28 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile14_node13 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,24] 3 profile14_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13,24] 3 profile14_node13_cert).mp (by decide +kernel))

def profile14_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node10 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13] 3 (by decide) (choices 2) [9,17,24] profile14_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,13] (choices 2) [9,17,24] profile14_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node11
  · exact profile14_node12
  · exact profile14_node13

def profile14_node14_cert : CutBound 5 := { lost := (rows 8 8 0 0 0), upper := (rows 23 23 13 13 29), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile14_node14 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,21] 3 profile14_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,21] 3 profile14_node14_cert).mp (by decide +kernel))

def profile14_node15_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 13 13 29), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile14_node15 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,25] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,25] 3 profile14_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,25] 3 profile14_node15_cert).mp (by decide +kernel))

def profile14_node16_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 30 13 13 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile14_node16 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,28] 3 profile14_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22,28] 3 profile14_node16_cert).mp (by decide +kernel))

def profile14_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node9 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile14_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [22] (choices 3) [13,21,25,28] profile14_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node10
  · exact profile14_node14
  · exact profile14_node15
  · exact profile14_node16

def profile14_node18_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 21 29 21), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile14_node18 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,13] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,13] 3 profile14_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,13] 3 profile14_node18_cert).mp (by decide +kernel))

def profile14_node19_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 13 13 29), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile14_node19 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,21] 3 profile14_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,21] 3 profile14_node19_cert).mp (by decide +kernel))

def profile14_node20_cert : CutBound 5 := { lost := (rows 4 0 0 0 0), upper := (rows 27 30 5 13 21), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile14_node20 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,28] 3 profile14_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26,28] 3 profile14_node20_cert).mp (by decide +kernel))

def profile14_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node17 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26] 3 (by decide) (choices 3) [13,21,28] profile14_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [26] (choices 3) [13,21,28] profile14_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node18
  · exact profile14_node19
  · exact profile14_node20

def profile14_node22_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 15 23 31 23), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile14_node22 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,13] 3 profile14_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,13] 3 profile14_node22_cert).mp (by decide +kernel))

def profile14_node23_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile14_node23 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,21] 3 profile14_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,21] 3 profile14_node23_cert).mp (by decide +kernel))

def profile14_node24_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 29 27 7 15 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile14_node24 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,25] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,25] 3 profile14_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,25] 3 profile14_node24_cert).mp (by decide +kernel))

def profile14_node25_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 7 15 23), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile14_node25 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,28] 3 profile14_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28,28] 3 profile14_node25_cert).mp (by decide +kernel))

def profile14_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node21 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28] 3 (by decide) (choices 3) [13,21,25,28] profile14_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [28] (choices 3) [13,21,25,28] profile14_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node22
  · exact profile14_node23
  · exact profile14_node24
  · exact profile14_node25

def profile14_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [] 3 := by
  apply routed_branch (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile14_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [] (choices 3) [14,22,26,28] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node1
  · exact profile14_node9
  · exact profile14_node17
  · exact profile14_node21

theorem profile14 : Upper (D (n:=5) [51,49,35,34,18]) (R (n:=5) [51,49,35,34,18]) [] 3 := profile14_node0

#print axioms profile14
end Delivery.FiveVertexPositive11
