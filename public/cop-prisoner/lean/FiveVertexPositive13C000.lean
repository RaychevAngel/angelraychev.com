import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 31 7 11 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30,29] 2 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30,29] 2 profile0_node2_cert).mp (by decide +kernel))

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30] 2 (by decide) (choices 4) [29] profile0_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [30] (choices 4) [29] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node2

def profile0_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [] 2 (by decide) (choices 4) [30] profile0_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [] (choices 4) [30] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=5) [68,67,34,34,18]) (R (n:=5) [68,67,34,34,18]) [] 2 := profile0_node0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile1_node2 : Upper (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30,29] 2 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30,29] 2 profile1_node2_cert).mp (by decide +kernel))

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30] 2 (by decide) (choices 4) [29] profile1_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [30] (choices 4) [29] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [] 2 (by decide) (choices 4) [30] profile1_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [] (choices 4) [30] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=5) [68,66,35,34,18]) (R (n:=5) [68,66,35,34,18]) [] 2 := profile1_node0

def profile2_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile2_node2 : Upper (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30,29] 2 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30,29] 2 profile2_node2_cert).mp (by decide +kernel))

def profile2_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30] 2 (by decide) (choices 4) [29] profile2_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [30] (choices 4) [29] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node2

def profile2_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [] 2 (by decide) (choices 4) [30] profile2_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [] (choices 4) [30] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [67,67,35,34,18]) (R (n:=5) [67,67,35,34,18]) [] 2 := profile2_node0

def profile3_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile3_node2 : Upper (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30,29] 2 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30,29] 2 profile3_node2_cert).mp (by decide +kernel))

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30] 2 (by decide) (choices 4) [29] profile3_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [30] (choices 4) [29] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [] 2 (by decide) (choices 4) [30] profile3_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [] (choices 4) [30] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node1

theorem profile3 : Upper (D (n:=5) [67,66,36,34,18]) (R (n:=5) [67,66,36,34,18]) [] 2 := profile3_node0

def profile4_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile4_node2 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,13] 2 profile4_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,13] 2 profile4_node2_cert).mp (by decide +kernel))

def profile4_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile4_node3 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,21] 2 profile4_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,21] 2 profile4_node3_cert).mp (by decide +kernel))

def profile4_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile4_node4 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,25] 2 profile4_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30,25] 2 profile4_node4_cert).mp (by decide +kernel))

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30] 2 (by decide) (choices 3) [13,21,25] profile4_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [30] (choices 3) [13,21,25] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node4

def profile4_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [] 2 (by decide) (choices 4) [30] profile4_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [] (choices 4) [30] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node1

theorem profile4 : Upper (D (n:=5) [68,51,50,34,18]) (R (n:=5) [68,51,50,34,18]) [] 2 := profile4_node0

def profile5_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile5_node2 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,13] 2 profile5_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,13] 2 profile5_node2_cert).mp (by decide +kernel))

def profile5_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile5_node3 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,21] 2 profile5_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,21] 2 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile5_node4 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,25] 2 profile5_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,25] 2 profile5_node4_cert).mp (by decide +kernel))

def profile5_node5_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 7 11 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile5_node5 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,28] 2 profile5_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30,28] 2 profile5_node5_cert).mp (by decide +kernel))

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile5_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [30] (choices 3) [13,21,25,28] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node4
  · exact profile5_node5

def profile5_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [] 2 (by decide) (choices 4) [30] profile5_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [] (choices 4) [30] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node1

theorem profile5 : Upper (D (n:=5) [67,52,50,34,18]) (R (n:=5) [67,52,50,34,18]) [] 2 := profile5_node0

def profile6_node2_cert : CutBound 5 := { lost := (rows 0 16 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node2 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,13] 2 profile6_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,13] 2 profile6_node2_cert).mp (by decide +kernel))

def profile6_node3_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node3 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,21] 2 profile6_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,21] 2 profile6_node3_cert).mp (by decide +kernel))

def profile6_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile6_node4 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,25] 2 profile6_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,25] 2 profile6_node4_cert).mp (by decide +kernel))

def profile6_node5_cert : CutBound 5 := { lost := (rows 0 1 8 0 0), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile6_node5 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,28] 2 profile6_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30,28] 2 profile6_node5_cert).mp (by decide +kernel))

def profile6_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node1 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile6_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [30] (choices 3) [13,21,25,28] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node2
  · exact profile6_node3
  · exact profile6_node4
  · exact profile6_node5

def profile6_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [] 2 (by decide) (choices 4) [30] profile6_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [] (choices 4) [30] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node1

theorem profile6 : Upper (D (n:=5) [67,51,51,34,18]) (R (n:=5) [67,51,51,34,18]) [] 2 := profile6_node0

def profile7_node2_cert : CutBound 5 := { lost := (rows 0 16 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile7_node2 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,13] 2 profile7_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,13] 2 profile7_node2_cert).mp (by decide +kernel))

def profile7_node3_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile7_node3 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,21] 2 profile7_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,21] 2 profile7_node3_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile7_node4 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,25] 2 profile7_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,25] 2 profile7_node4_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 5 := { lost := (rows 0 1 8 0 0), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile7_node5 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,28] 2 profile7_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30,28] 2 profile7_node5_cert).mp (by decide +kernel))

def profile7_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile7_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [30] (choices 3) [13,21,25,28] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node4
  · exact profile7_node5

def profile7_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [] 2 (by decide) (choices 4) [30] profile7_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [] (choices 4) [30] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node1

theorem profile7 : Upper (D (n:=5) [66,52,51,34,18]) (R (n:=5) [66,52,51,34,18]) [] 2 := profile7_node0

def profile8_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile8_node2 : Upper (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30,29] 2 profile8_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30,29] 2 profile8_node2_cert).mp (by decide +kernel))

def profile8_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30] 2 (by decide) (choices 4) [29] profile8_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [30] (choices 4) [29] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node2

def profile8_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [] 2 (by decide) (choices 4) [30] profile8_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [] (choices 4) [30] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node1

theorem profile8 : Upper (D (n:=5) [67,66,35,35,18]) (R (n:=5) [67,66,35,35,18]) [] 2 := profile8_node0

def profile9_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile9_node2 : Upper (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30,29] 2 profile9_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30,29] 2 profile9_node2_cert).mp (by decide +kernel))

def profile9_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30] 2 (by decide) (choices 4) [29] profile9_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [30] (choices 4) [29] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node2

def profile9_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [] 2 (by decide) (choices 4) [30] profile9_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [] (choices 4) [30] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=5) [66,66,36,35,18]) (R (n:=5) [66,66,36,35,18]) [] 2 := profile9_node0

def profile10_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile10_node2 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,13] 2 profile10_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,13] 2 profile10_node2_cert).mp (by decide +kernel))

def profile10_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile10_node3 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,21] 2 profile10_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,21] 2 profile10_node3_cert).mp (by decide +kernel))

def profile10_node4_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile10_node4 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,25] 2 profile10_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30,25] 2 profile10_node4_cert).mp (by decide +kernel))

def profile10_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node1 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30] 2 (by decide) (choices 3) [13,21,25] profile10_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [30] (choices 3) [13,21,25] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node2
  · exact profile10_node3
  · exact profile10_node4

def profile10_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [] 2 (by decide) (choices 4) [30] profile10_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [] (choices 4) [30] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=5) [68,50,50,35,18]) (R (n:=5) [68,50,50,35,18]) [] 2 := profile10_node0

def profile11_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile11_node2 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,13] 2 profile11_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,13] 2 profile11_node2_cert).mp (by decide +kernel))

def profile11_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile11_node3 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,21] 2 profile11_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,21] 2 profile11_node3_cert).mp (by decide +kernel))

def profile11_node4_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile11_node4 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,25] 2 profile11_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,25] 2 profile11_node4_cert).mp (by decide +kernel))

def profile11_node5_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile11_node5 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,28] 2 profile11_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30,28] 2 profile11_node5_cert).mp (by decide +kernel))

def profile11_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node1 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile11_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [30] (choices 3) [13,21,25,28] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node2
  · exact profile11_node3
  · exact profile11_node4
  · exact profile11_node5

def profile11_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node0 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [] 2 (by decide) (choices 4) [30] profile11_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [] (choices 4) [30] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node1

theorem profile11 : Upper (D (n:=5) [67,51,50,35,18]) (R (n:=5) [67,51,50,35,18]) [] 2 := profile11_node0

def profile12_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile12_node2 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,13] 2 profile12_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,13] 2 profile12_node2_cert).mp (by decide +kernel))

def profile12_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile12_node3 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,21] 2 profile12_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,21] 2 profile12_node3_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile12_node4 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,25] 2 profile12_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,25] 2 profile12_node4_cert).mp (by decide +kernel))

def profile12_node5_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile12_node5 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,28] 2 profile12_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30,28] 2 profile12_node5_cert).mp (by decide +kernel))

def profile12_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node1 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile12_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [30] (choices 3) [13,21,25,28] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node4
  · exact profile12_node5

def profile12_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node0 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [] 2 (by decide) (choices 4) [30] profile12_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [] (choices 4) [30] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node1

theorem profile12 : Upper (D (n:=5) [66,52,50,35,18]) (R (n:=5) [66,52,50,35,18]) [] 2 := profile12_node0

def profile13_node3_cert : CutBound 5 := { lost := (rows 0 16 16 1 0), upper := (rows 31 15 15 30 22), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile13_node3 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,11] 2 profile13_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,11] 2 profile13_node3_cert).mp (by decide +kernel))

def profile13_node4_cert : CutBound 5 := { lost := (rows 0 0 8 1 0), upper := (rows 31 15 23 14 30), lower := (rows 31 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile13_node4 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,19] 2 profile13_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,19] 2 profile13_node4_cert).mp (by decide +kernel))

def profile13_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 15 29 14 22), lower := (rows 31 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) }] }

theorem profile13_node5 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,25] 2 profile13_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,25] 2 profile13_node5_cert).mp (by decide +kernel))

def profile13_node6_cert : CutBound 5 := { lost := (rows 0 16 1 16 0), upper := (rows 31 15 30 15 23), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile13_node6 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,26] 2 profile13_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13,26] 2 profile13_node6_cert).mp (by decide +kernel))

def profile13_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node2 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13] 2 (by decide) (choices 3) [11,19,25,26] profile13_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,13] (choices 3) [11,19,25,26] profile13_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node3
  · exact profile13_node4
  · exact profile13_node5
  · exact profile13_node6

def profile13_node7_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile13_node7 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,21] 2 profile13_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,21] 2 profile13_node7_cert).mp (by decide +kernel))

def profile13_node8_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile13_node8 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,25] 2 profile13_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,25] 2 profile13_node8_cert).mp (by decide +kernel))

def profile13_node9_cert : CutBound 5 := { lost := (rows 0 1 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile13_node9 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,28] 2 profile13_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30,28] 2 profile13_node9_cert).mp (by decide +kernel))

def profile13_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node1 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile13_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [30] (choices 3) [13,21,25,28] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node7
  · exact profile13_node8
  · exact profile13_node9

def profile13_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [] 2 (by decide) (choices 4) [30] profile13_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [] (choices 4) [30] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=5) [66,51,51,35,18]) (R (n:=5) [66,51,51,35,18]) [] 2 := profile13_node0

def profile14_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile14_node2 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,13] 2 profile14_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,13] 2 profile14_node2_cert).mp (by decide +kernel))

def profile14_node3_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile14_node3 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,25] 2 profile14_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,25] 2 profile14_node3_cert).mp (by decide +kernel))

def profile14_node4_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile14_node4 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,28] 2 profile14_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30,28] 2 profile14_node4_cert).mp (by decide +kernel))

def profile14_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30] 2 (by decide) (choices 3) [13,25,28] profile14_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [30] (choices 3) [13,25,28] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node3
  · exact profile14_node4

def profile14_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [] 2 (by decide) (choices 4) [30] profile14_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [] (choices 4) [30] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node1

theorem profile14 : Upper (D (n:=5) [67,50,50,36,18]) (R (n:=5) [67,50,50,36,18]) [] 2 := profile14_node0

def profile15_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile15_node2 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,13] 2 profile15_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,13] 2 profile15_node2_cert).mp (by decide +kernel))

def profile15_node3_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 31 27 15 15 31), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile15_node3 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,25] 2 profile15_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,25] 2 profile15_node3_cert).mp (by decide +kernel))

def profile15_node4_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile15_node4 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,28] 2 profile15_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30,28] 2 profile15_node4_cert).mp (by decide +kernel))

def profile15_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30] 2 (by decide) (choices 3) [13,25,28] profile15_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [30] (choices 3) [13,25,28] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node2
  · exact profile15_node3
  · exact profile15_node4

def profile15_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [] 2 (by decide) (choices 4) [30] profile15_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [] (choices 4) [30] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node1

theorem profile15 : Upper (D (n:=5) [66,51,50,36,18]) (R (n:=5) [66,51,50,36,18]) [] 2 := profile15_node0

def profile16_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile16_node2 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,13] 2 profile16_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,13] 2 profile16_node2_cert).mp (by decide +kernel))

def profile16_node4_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 23 15 27 19), lower := (rows 15 23 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile16_node4 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,11] 2 profile16_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,11] 2 profile16_node4_cert).mp (by decide +kernel))

def profile16_node5_cert : CutBound 5 := { lost := (rows 0 8 8 4 0), upper := (rows 15 23 23 11 27), lower := (rows 15 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile16_node5 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,19] 2 profile16_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,19] 2 profile16_node5_cert).mp (by decide +kernel))

def profile16_node6_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 23 29 11 19), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile16_node6 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,25] 2 profile16_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21,25] 2 profile16_node6_cert).mp (by decide +kernel))

def profile16_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node3 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21] 2 (by decide) (choices 3) [11,19,25] profile16_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14,21] (choices 3) [11,19,25] profile16_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node4
  · exact profile16_node5
  · exact profile16_node6

def profile16_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile16_node1 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14] 2 (by decide) (choices 3) [13,21] profile16_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [14] (choices 3) [13,21] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node2
  · exact profile16_node3

def profile16_node9_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 15 15 27 19), lower := (rows 23 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile16_node9 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,11] 2 profile16_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,11] 2 profile16_node9_cert).mp (by decide +kernel))

def profile16_node10_cert : CutBound 5 := { lost := (rows 8 0 8 4 0), upper := (rows 23 15 23 11 27), lower := (rows 23 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile16_node10 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,19] 2 profile16_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,19] 2 profile16_node10_cert).mp (by decide +kernel))

def profile16_node11_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 15 29 11 19), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile16_node11 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,25] 2 profile16_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13,25] 2 profile16_node11_cert).mp (by decide +kernel))

def profile16_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node8 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13] 2 (by decide) (choices 3) [11,19,25] profile16_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,13] (choices 3) [11,19,25] profile16_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node9
  · exact profile16_node10
  · exact profile16_node11

def profile16_node12_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 15 11 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node12 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,21] 2 profile16_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,21] 2 profile16_node12_cert).mp (by decide +kernel))

def profile16_node13_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 15 15 31), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile16_node13 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,25] 2 profile16_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22,25] 2 profile16_node13_cert).mp (by decide +kernel))

def profile16_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node7 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22] 2 (by decide) (choices 3) [13,21,25] profile16_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [22] (choices 3) [13,21,25] profile16_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node8
  · exact profile16_node12
  · exact profile16_node13

def profile16_node15_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile16_node15 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,13] 2 profile16_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,13] 2 profile16_node15_cert).mp (by decide +kernel))

def profile16_node16_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 29 23 15 11 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node16 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,21] 2 profile16_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28,21] 2 profile16_node16_cert).mp (by decide +kernel))

def profile16_node14_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile16_node14 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28] 2 (by decide) (choices 3) [13,21] profile16_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [28] (choices 3) [13,21] profile16_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node15
  · exact profile16_node16

def profile16_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile16_node0 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [] 2 (by decide) (choices 3) [14,22,28] profile16_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [] (choices 3) [14,22,28] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node1
  · exact profile16_node7
  · exact profile16_node14

theorem profile16 : Upper (D (n:=5) [52,51,50,50,18]) (R (n:=5) [52,51,50,50,18]) [] 2 := profile16_node0

def profile17_node2_cert : CutBound 5 := { lost := (rows 16 16 8 0 0), upper := (rows 15 15 23 31 23), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node2 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,13] 2 profile17_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,13] 2 profile17_node2_cert).mp (by decide +kernel))

def profile17_node4_cert : CutBound 5 := { lost := (rows 16 8 16 0 0), upper := (rows 15 23 15 31 23), lower := (rows 15 23 15 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile17_node4 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,11] 2 profile17_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,11] 2 profile17_node4_cert).mp (by decide +kernel))

def profile17_node5_cert : CutBound 5 := { lost := (rows 0 8 8 0 0), upper := (rows 15 23 23 15 31), lower := (rows 15 23 23 8 16), losses := [{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile17_node5 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,19] 2 profile17_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,19] 2 profile17_node5_cert).mp (by decide +kernel))

def profile17_node6_cert : CutBound 5 := { lost := (rows 16 8 0 16 0), upper := (rows 15 23 29 15 23), lower := (rows 15 23 29 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile17_node6 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,25] 2 profile17_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,25] 2 profile17_node6_cert).mp (by decide +kernel))

def profile17_node7_cert : CutBound 5 := { lost := (rows 16 8 0 16 0), upper := (rows 15 23 30 15 23), lower := (rows 15 23 30 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile17_node7 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,26] 2 profile17_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21,26] 2 profile17_node7_cert).mp (by decide +kernel))

def profile17_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node3 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21] 2 (by decide) (choices 3) [11,19,25,26] profile17_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,21] (choices 3) [11,19,25,26] profile17_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile17_node4
  · exact profile17_node5
  · exact profile17_node6
  · exact profile17_node7

def profile17_node9_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 27 23 15 23), lower := (rows 15 27 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile17_node9 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25,19] 2 profile17_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25,19] 2 profile17_node9_cert).mp (by decide +kernel))

def profile17_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node8 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25] 2 (by decide) (choices 3) [19] profile17_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,25] (choices 3) [19] profile17_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node9

def profile17_node10_cert : CutBound 5 := { lost := (rows 16 0 8 0 0), upper := (rows 15 30 23 31 23), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node10 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,28] 2 profile17_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14,28] 2 profile17_node10_cert).mp (by decide +kernel))

def profile17_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node1 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile17_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [14] (choices 3) [13,21,25,28] profile17_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile17_node2
  · exact profile17_node3
  · exact profile17_node8
  · exact profile17_node10

def profile17_node13_cert : CutBound 5 := { lost := (rows 8 16 16 0 0), upper := (rows 23 15 15 31 23), lower := (rows 23 15 15 8 16), losses := [{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile17_node13 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,11] 2 profile17_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,11] 2 profile17_node13_cert).mp (by decide +kernel))

def profile17_node14_cert : CutBound 5 := { lost := (rows 8 0 8 0 0), upper := (rows 23 15 23 15 31), lower := (rows 23 15 23 8 16), losses := [{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile17_node14 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,19] 2 profile17_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,19] 2 profile17_node14_cert).mp (by decide +kernel))

def profile17_node15_cert : CutBound 5 := { lost := (rows 8 16 0 16 0), upper := (rows 23 15 29 15 23), lower := (rows 23 15 29 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile17_node15 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,25] 2 profile17_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,25] 2 profile17_node15_cert).mp (by decide +kernel))

def profile17_node16_cert : CutBound 5 := { lost := (rows 8 16 0 16 0), upper := (rows 23 15 30 15 23), lower := (rows 23 15 30 8 16), losses := [{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile17_node16 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,26] 2 profile17_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13,26] 2 profile17_node16_cert).mp (by decide +kernel))

def profile17_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node12 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13] 2 (by decide) (choices 3) [11,19,25,26] profile17_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,13] (choices 3) [11,19,25,26] profile17_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile17_node13
  · exact profile17_node14
  · exact profile17_node15
  · exact profile17_node16

def profile17_node17_cert : CutBound 5 := { lost := (rows 8 8 0 0 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile17_node17 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,21] 2 profile17_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,21] 2 profile17_node17_cert).mp (by decide +kernel))

def profile17_node18_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 15 15 31), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node18 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,25] 2 profile17_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,25] 2 profile17_node18_cert).mp (by decide +kernel))

def profile17_node19_cert : CutBound 5 := { lost := (rows 8 0 16 16 0), upper := (rows 23 30 15 15 31), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile17_node19 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,28] 2 profile17_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22,28] 2 profile17_node19_cert).mp (by decide +kernel))

def profile17_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node11 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22] 2 (by decide) (choices 3) [13,21,25,28] profile17_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [22] (choices 3) [13,21,25,28] profile17_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile17_node12
  · exact profile17_node17
  · exact profile17_node18
  · exact profile17_node19

def profile17_node22_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 27 15 23 15 23), lower := (rows 27 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile17_node22 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13,19] 2 profile17_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13,19] 2 profile17_node22_cert).mp (by decide +kernel))

def profile17_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node21 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13] 2 (by decide) (choices 3) [19] profile17_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,13] (choices 3) [19] profile17_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node22

def profile17_node23_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 15 15 31), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node23 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,21] 2 profile17_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,21] 2 profile17_node23_cert).mp (by decide +kernel))

def profile17_node24_cert : CutBound 5 := { lost := (rows 4 0 8 0 0), upper := (rows 27 30 7 15 23), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile17_node24 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,28] 2 profile17_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26,28] 2 profile17_node24_cert).mp (by decide +kernel))

def profile17_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node20 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26] 2 (by decide) (choices 3) [13,21,28] profile17_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [26] (choices 3) [13,21,28] profile17_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node21
  · exact profile17_node23
  · exact profile17_node24

def profile17_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile17_node0 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [] 2 (by decide) (choices 3) [14,22,26] profile17_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [] (choices 3) [14,22,26] profile17_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node1
  · exact profile17_node11
  · exact profile17_node20

theorem profile17 : Upper (D (n:=5) [51,51,51,50,18]) (R (n:=5) [51,51,51,50,18]) [] 2 := profile17_node0

def profile18_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile18_node2 : Upper (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30,29] 2 profile18_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30,29] 2 profile18_node2_cert).mp (by decide +kernel))

def profile18_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node1 : Upper (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30] 2 (by decide) (choices 4) [29] profile18_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [30] (choices 4) [29] profile18_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node2

def profile18_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node0 : Upper (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [] 2 (by decide) (choices 4) [30] profile18_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [] (choices 4) [30] profile18_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node1

theorem profile18 : Upper (D (n:=5) [68,66,34,34,19]) (R (n:=5) [68,66,34,34,19]) [] 2 := profile18_node0

def profile19_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile19_node2 : Upper (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30,29] 2 profile19_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30,29] 2 profile19_node2_cert).mp (by decide +kernel))

def profile19_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node1 : Upper (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30] 2 (by decide) (choices 4) [29] profile19_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [30] (choices 4) [29] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node2

def profile19_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [] 2 (by decide) (choices 4) [30] profile19_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [] (choices 4) [30] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=5) [67,67,34,34,19]) (R (n:=5) [67,67,34,34,19]) [] 2 := profile19_node0

def profile20_node3_cert : CutBound 5 := { lost := (rows 0 0 8 2 0), upper := (rows 31 31 7 29 21), lower := (rows 31 31 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile20_node3 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,3] 2 profile20_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,3] 2 profile20_node3_cert).mp (by decide +kernel))

def profile20_node4_cert : CutBound 5 := { lost := (rows 0 0 10 0 0), upper := (rows 31 31 21 15 23), lower := (rows 31 31 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile20_node4 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,17] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,17] 2 profile20_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,17] 2 profile20_node4_cert).mp (by decide +kernel))

def profile20_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 31 22 13 21), lower := (rows 31 31 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile20_node5 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,18] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,18] 2 profile20_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29,18] 2 profile20_node5_cert).mp (by decide +kernel))

def profile20_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node2 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29] 2 (by decide) (choices 2) [3,17,18] profile20_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30,29] (choices 2) [3,17,18] profile20_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile20_node3
  · exact profile20_node4
  · exact profile20_node5

def profile20_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node1 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30] 2 (by decide) (choices 4) [29] profile20_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [30] (choices 4) [29] profile20_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node2

def profile20_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node0 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [] 2 (by decide) (choices 4) [30] profile20_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [] (choices 4) [30] profile20_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node1

theorem profile20 : Upper (D (n:=5) [67,66,35,34,19]) (R (n:=5) [67,66,35,34,19]) [] 2 := profile20_node0

def profile21_node3_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 31 31 7 28 20), lower := (rows 31 31 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile21_node3 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,3] 2 profile21_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,3] 2 profile21_node3_cert).mp (by decide +kernel))

def profile21_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 31 21 14 22), lower := (rows 31 31 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 21 8 16) }] }

theorem profile21_node4 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,17] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,17] 2 profile21_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,17] 2 profile21_node4_cert).mp (by decide +kernel))

def profile21_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 31 22 13 21), lower := (rows 31 31 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile21_node5 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,18] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,18] 2 profile21_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29,18] 2 profile21_node5_cert).mp (by decide +kernel))

def profile21_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node2 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29] 2 (by decide) (choices 2) [3,17,18] profile21_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30,29] (choices 2) [3,17,18] profile21_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node3
  · exact profile21_node4
  · exact profile21_node5

def profile21_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30] 2 (by decide) (choices 4) [29] profile21_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [30] (choices 4) [29] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node2

def profile21_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [] 2 (by decide) (choices 4) [30] profile21_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [] (choices 4) [30] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node1

theorem profile21 : Upper (D (n:=5) [66,66,36,34,19]) (R (n:=5) [66,66,36,34,19]) [] 2 := profile21_node0

def profile22_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile22_node2 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,13] 2 profile22_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,13] 2 profile22_node2_cert).mp (by decide +kernel))

def profile22_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile22_node3 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,21] 2 profile22_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,21] 2 profile22_node3_cert).mp (by decide +kernel))

def profile22_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile22_node4 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,25] 2 profile22_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30,25] 2 profile22_node4_cert).mp (by decide +kernel))

def profile22_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node1 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30] 2 (by decide) (choices 3) [13,21,25] profile22_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [30] (choices 3) [13,21,25] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile22_node2
  · exact profile22_node3
  · exact profile22_node4

def profile22_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [] 2 (by decide) (choices 4) [30] profile22_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [] (choices 4) [30] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=5) [68,50,50,34,19]) (R (n:=5) [68,50,50,34,19]) [] 2 := profile22_node0

def profile23_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile23_node2 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,13] 2 profile23_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,13] 2 profile23_node2_cert).mp (by decide +kernel))

def profile23_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile23_node3 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,21] 2 profile23_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,21] 2 profile23_node3_cert).mp (by decide +kernel))

def profile23_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile23_node4 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,25] 2 profile23_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,25] 2 profile23_node4_cert).mp (by decide +kernel))

def profile23_node5_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile23_node5 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,28] 2 profile23_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30,28] 2 profile23_node5_cert).mp (by decide +kernel))

def profile23_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node1 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile23_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [30] (choices 3) [13,21,25,28] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile23_node2
  · exact profile23_node3
  · exact profile23_node4
  · exact profile23_node5

def profile23_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [] 2 (by decide) (choices 4) [30] profile23_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [] (choices 4) [30] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=5) [67,51,50,34,19]) (R (n:=5) [67,51,50,34,19]) [] 2 := profile23_node0

def profile24_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile24_node2 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,13] 2 profile24_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,13] 2 profile24_node2_cert).mp (by decide +kernel))

def profile24_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile24_node3 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,21] 2 profile24_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,21] 2 profile24_node3_cert).mp (by decide +kernel))

def profile24_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile24_node4 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,25] 2 profile24_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,25] 2 profile24_node4_cert).mp (by decide +kernel))

def profile24_node5_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile24_node5 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,28] 2 profile24_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30,28] 2 profile24_node5_cert).mp (by decide +kernel))

def profile24_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile24_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [30] (choices 3) [13,21,25,28] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node2
  · exact profile24_node3
  · exact profile24_node4
  · exact profile24_node5

def profile24_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [] 2 (by decide) (choices 4) [30] profile24_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [] (choices 4) [30] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=5) [66,52,50,34,19]) (R (n:=5) [66,52,50,34,19]) [] 2 := profile24_node0

def profile25_node2_cert : CutBound 5 := { lost := (rows 0 16 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile25_node2 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,13] 2 profile25_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,13] 2 profile25_node2_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 5 := { lost := (rows 0 8 0 1 0), upper := (rows 31 23 15 30 22), lower := (rows 31 23 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile25_node4 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,11] 2 profile25_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,11] 2 profile25_node4_cert).mp (by decide +kernel))

def profile25_node5_cert : CutBound 5 := { lost := (rows 0 8 8 1 0), upper := (rows 31 23 23 14 30), lower := (rows 31 23 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile25_node5 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,19] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,19] 2 profile25_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,19] 2 profile25_node5_cert).mp (by decide +kernel))

def profile25_node6_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 23 29 14 22), lower := (rows 31 23 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile25_node6 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,25] 2 profile25_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,25] 2 profile25_node6_cert).mp (by decide +kernel))

def profile25_node7_cert : CutBound 5 := { lost := (rows 0 8 1 0 0), upper := (rows 31 23 30 15 23), lower := (rows 31 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile25_node7 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,26] 2 profile25_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21,26] 2 profile25_node7_cert).mp (by decide +kernel))

def profile25_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node3 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21] 2 (by decide) (choices 3) [11,19,25,26] profile25_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,21] (choices 3) [11,19,25,26] profile25_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile25_node4
  · exact profile25_node5
  · exact profile25_node6
  · exact profile25_node7

def profile25_node8_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile25_node8 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,25] 2 profile25_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,25] 2 profile25_node8_cert).mp (by decide +kernel))

def profile25_node9_cert : CutBound 5 := { lost := (rows 0 1 8 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile25_node9 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,28] 2 profile25_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30,28] 2 profile25_node9_cert).mp (by decide +kernel))

def profile25_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node1 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile25_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [30] (choices 3) [13,21,25,28] profile25_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile25_node2
  · exact profile25_node3
  · exact profile25_node8
  · exact profile25_node9

def profile25_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node0 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [] 2 (by decide) (choices 4) [30] profile25_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [] (choices 4) [30] profile25_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node1

theorem profile25 : Upper (D (n:=5) [66,51,51,34,19]) (R (n:=5) [66,51,51,34,19]) [] 2 := profile25_node0

def profile26_node3_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 31 31 7 28 28), lower := (rows 31 31 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile26_node3 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,3] 2 profile26_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,3] 2 profile26_node3_cert).mp (by decide +kernel))

def profile26_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 31 13 30 22), lower := (rows 31 31 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) }] }

theorem profile26_node4 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,9] 2 profile26_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,9] 2 profile26_node4_cert).mp (by decide +kernel))

def profile26_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 31 14 29 21), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile26_node5 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,10] 2 profile26_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,10] 2 profile26_node5_cert).mp (by decide +kernel))

def profile26_node6_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 31 21 14 30), lower := (rows 31 31 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 21 8 16) }] }

theorem profile26_node6 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,17] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,17] 2 profile26_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,17] 2 profile26_node6_cert).mp (by decide +kernel))

def profile26_node7_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 31 22 13 29), lower := (rows 31 31 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile26_node7 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,18] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,18] 2 profile26_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,18] 2 profile26_node7_cert).mp (by decide +kernel))

def profile26_node8_cert : CutBound 5 := { lost := (rows 0 0 3 0 0), upper := (rows 31 31 28 15 23), lower := (rows 31 31 28 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 28 8 16) }] }

theorem profile26_node8 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,24] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,24] 2 profile26_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29,24] 2 profile26_node8_cert).mp (by decide +kernel))

def profile26_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node2 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile26_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30,29] (choices 2) [3,9,10,17,18,24] profile26_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node3
  · exact profile26_node4
  · exact profile26_node5
  · exact profile26_node6
  · exact profile26_node7
  · exact profile26_node8

def profile26_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30] 2 (by decide) (choices 4) [29] profile26_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [30] (choices 4) [29] profile26_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node2

def profile26_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node0 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [] 2 (by decide) (choices 4) [30] profile26_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [] (choices 4) [30] profile26_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node1

theorem profile26 : Upper (D (n:=5) [66,66,35,35,19]) (R (n:=5) [66,66,35,35,19]) [] 2 := profile26_node0

#print axioms profile26
end Delivery.FiveVertexPositive13
