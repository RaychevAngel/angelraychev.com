import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive13
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile27_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile27_node2 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,13] 2 profile27_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,13] 2 profile27_node2_cert).mp (by decide +kernel))

def profile27_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile27_node3 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,21] 2 profile27_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,21] 2 profile27_node3_cert).mp (by decide +kernel))

def profile27_node5_cert : CutBound 5 := { lost := (rows 0 4 0 2 0), upper := (rows 31 27 15 29 21), lower := (rows 31 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) }] }

theorem profile27_node5 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,11] 2 profile27_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,11] 2 profile27_node5_cert).mp (by decide +kernel))

def profile27_node6_cert : CutBound 5 := { lost := (rows 0 4 0 2 0), upper := (rows 31 27 23 13 29), lower := (rows 31 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 19 8 16) }] }

theorem profile27_node6 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,19] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,19] 2 profile27_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,19] 2 profile27_node6_cert).mp (by decide +kernel))

def profile27_node7_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 31 27 29 15 23), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile27_node7 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,25] 2 profile27_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,25] 2 profile27_node7_cert).mp (by decide +kernel))

def profile27_node8_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 27 30 13 21), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) }] }

theorem profile27_node8 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,26] 2 profile27_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25,26] 2 profile27_node8_cert).mp (by decide +kernel))

def profile27_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node4 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25] 2 (by decide) (choices 3) [11,19,25,26] profile27_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,25] (choices 3) [11,19,25,26] profile27_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile27_node5
  · exact profile27_node6
  · exact profile27_node7
  · exact profile27_node8

def profile27_node9_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile27_node9 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,28] 2 profile27_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30,28] 2 profile27_node9_cert).mp (by decide +kernel))

def profile27_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile27_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [30] (choices 3) [13,21,25,28] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile27_node2
  · exact profile27_node3
  · exact profile27_node4
  · exact profile27_node9

def profile27_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [] 2 (by decide) (choices 4) [30] profile27_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [] (choices 4) [30] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=5) [67,50,50,35,19]) (R (n:=5) [67,50,50,35,19]) [] 2 := profile27_node0

def profile28_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile28_node2 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,13] 2 profile28_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,13] 2 profile28_node2_cert).mp (by decide +kernel))

def profile28_node3_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile28_node3 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,21] 2 profile28_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,21] 2 profile28_node3_cert).mp (by decide +kernel))

def profile28_node5_cert : CutBound 5 := { lost := (rows 0 4 0 1 0), upper := (rows 31 27 15 30 22), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) }] }

theorem profile28_node5 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,11] 2 profile28_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,11] 2 profile28_node5_cert).mp (by decide +kernel))

def profile28_node6_cert : CutBound 5 := { lost := (rows 0 4 0 1 0), upper := (rows 31 27 23 14 30), lower := (rows 31 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 19 8 16) }] }

theorem profile28_node6 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,19] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,19] 2 profile28_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,19] 2 profile28_node6_cert).mp (by decide +kernel))

def profile28_node7_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 27 29 14 22), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile28_node7 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,25] 2 profile28_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,25] 2 profile28_node7_cert).mp (by decide +kernel))

def profile28_node8_cert : CutBound 5 := { lost := (rows 0 4 1 0 0), upper := (rows 31 27 30 15 23), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) }] }

theorem profile28_node8 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,26] 2 profile28_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25,26] 2 profile28_node8_cert).mp (by decide +kernel))

def profile28_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node4 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25] 2 (by decide) (choices 3) [11,19,25,26] profile28_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,25] (choices 3) [11,19,25,26] profile28_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node5
  · exact profile28_node6
  · exact profile28_node7
  · exact profile28_node8

def profile28_node9_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile28_node9 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,28] 2 profile28_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30,28] 2 profile28_node9_cert).mp (by decide +kernel))

def profile28_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node1 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile28_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [30] (choices 3) [13,21,25,28] profile28_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node2
  · exact profile28_node3
  · exact profile28_node4
  · exact profile28_node9

def profile28_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [] 2 (by decide) (choices 4) [30] profile28_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [] (choices 4) [30] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node1

theorem profile28 : Upper (D (n:=5) [66,51,50,35,19]) (R (n:=5) [66,51,50,35,19]) [] 2 := profile28_node0

def profile29_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 31 15 31 27 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile29_node2 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,13] 2 profile29_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,13] 2 profile29_node2_cert).mp (by decide +kernel))

def profile29_node4_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 31 27 15 28 28), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile29_node4 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,11] 2 profile29_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,11] 2 profile29_node4_cert).mp (by decide +kernel))

def profile29_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 27 29 14 30), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile29_node5 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,25] 2 profile29_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,25] 2 profile29_node5_cert).mp (by decide +kernel))

def profile29_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 27 30 13 29), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) }] }

theorem profile29_node6 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,26] 2 profile29_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25,26] 2 profile29_node6_cert).mp (by decide +kernel))

def profile29_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node3 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile29_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,25] (choices 3) [11,25,26] profile29_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node4
  · exact profile29_node5
  · exact profile29_node6

def profile29_node7_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile29_node7 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,28] 2 profile29_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30,28] 2 profile29_node7_cert).mp (by decide +kernel))

def profile29_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node1 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30] 2 (by decide) (choices 3) [13,25,28] profile29_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [30] (choices 3) [13,25,28] profile29_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node2
  · exact profile29_node3
  · exact profile29_node7

def profile29_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node0 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [] 2 (by decide) (choices 4) [30] profile29_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [] (choices 4) [30] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node1

theorem profile29 : Upper (D (n:=5) [66,50,50,36,19]) (R (n:=5) [66,50,50,36,19]) [] 2 := profile29_node0

def profile30_node3_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 15 23 23 25 25), lower := (rows 15 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile30_node3 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,19] 2 profile30_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,19] 2 profile30_node3_cert).mp (by decide +kernel))

def profile30_node4_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 23 29 27 19), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile30_node4 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,25] 2 profile30_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21,25] 2 profile30_node4_cert).mp (by decide +kernel))

def profile30_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node2 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21] 2 (by decide) (choices 3) [19,25] profile30_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14,21] (choices 3) [19,25] profile30_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node3
  · exact profile30_node4

def profile30_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile30_node1 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14] 2 (by decide) (choices 3) [21] profile30_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [14] (choices 3) [21] profile30_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile30_node2

def profile30_node7_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 23 15 23 25 25), lower := (rows 23 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile30_node7 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,19] 2 profile30_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,19] 2 profile30_node7_cert).mp (by decide +kernel))

def profile30_node8_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 15 29 27 19), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile30_node8 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,25] 2 profile30_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13,25] 2 profile30_node8_cert).mp (by decide +kernel))

def profile30_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node6 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13] 2 (by decide) (choices 3) [19,25] profile30_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,13] (choices 3) [19,25] profile30_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node7
  · exact profile30_node8

def profile30_node9_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile30_node9 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,21] 2 profile30_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,21] 2 profile30_node9_cert).mp (by decide +kernel))

def profile30_node11_cert : CutBound 5 := { lost := (rows 8 0 0 2 0), upper := (rows 23 27 15 29 21), lower := (rows 23 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile30_node11 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,11] 2 profile30_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,11] 2 profile30_node11_cert).mp (by decide +kernel))

def profile30_node12_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 27 23 13 29), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile30_node12 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,19] 2 profile30_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,19] 2 profile30_node12_cert).mp (by decide +kernel))

def profile30_node13_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 23 27 29 15 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) }] }

theorem profile30_node13 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,25] 2 profile30_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25,25] 2 profile30_node13_cert).mp (by decide +kernel))

def profile30_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node10 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25] 2 (by decide) (choices 3) [11,19,25] profile30_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22,25] (choices 3) [11,19,25] profile30_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node11
  · exact profile30_node12
  · exact profile30_node13

def profile30_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node5 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22] 2 (by decide) (choices 3) [13,21,25] profile30_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [22] (choices 3) [13,21,25] profile30_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node6
  · exact profile30_node9
  · exact profile30_node10

def profile30_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile30_node0 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [] 2 (by decide) (choices 3) [14,22] profile30_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [] (choices 3) [14,22] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node1
  · exact profile30_node5

theorem profile30 : Upper (D (n:=5) [52,50,50,50,19]) (R (n:=5) [52,50,50,50,19]) [] 2 := profile30_node0

def profile31_node3_cert : CutBound 5 := { lost := (rows 0 8 8 4 0), upper := (rows 15 23 23 27 27), lower := (rows 15 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile31_node3 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,19] 2 profile31_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,19] 2 profile31_node3_cert).mp (by decide +kernel))

def profile31_node4_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 23 29 27 19), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile31_node4 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,25] 2 profile31_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,25] 2 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 15 23 30 27 19), lower := (rows 15 23 30 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile31_node5 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,26] 2 profile31_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21,26] 2 profile31_node5_cert).mp (by decide +kernel))

def profile31_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node2 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21] 2 (by decide) (choices 3) [19,25,26] profile31_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,21] (choices 3) [19,25,26] profile31_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node3
  · exact profile31_node4
  · exact profile31_node5

def profile31_node6_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 15 30 23 27 19), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile31_node6 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,28] 2 profile31_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14,28] 2 profile31_node6_cert).mp (by decide +kernel))

def profile31_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile31_node1 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14] 2 (by decide) (choices 3) [21,28] profile31_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [14] (choices 3) [21,28] profile31_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node2
  · exact profile31_node6

def profile31_node9_cert : CutBound 5 := { lost := (rows 8 0 8 4 0), upper := (rows 23 15 23 27 27), lower := (rows 23 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile31_node9 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,19] 2 profile31_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,19] 2 profile31_node9_cert).mp (by decide +kernel))

def profile31_node10_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 15 29 27 19), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile31_node10 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,25] 2 profile31_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,25] 2 profile31_node10_cert).mp (by decide +kernel))

def profile31_node11_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 15 30 27 19), lower := (rows 23 15 30 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile31_node11 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,26] 2 profile31_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13,26] 2 profile31_node11_cert).mp (by decide +kernel))

def profile31_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node8 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13] 2 (by decide) (choices 3) [19,25,26] profile31_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,13] (choices 3) [19,25,26] profile31_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node9
  · exact profile31_node10
  · exact profile31_node11

def profile31_node12_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile31_node12 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,21] 2 profile31_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,21] 2 profile31_node12_cert).mp (by decide +kernel))

def profile31_node14_cert : CutBound 5 := { lost := (rows 8 0 16 0 0), upper := (rows 23 27 15 31 23), lower := (rows 23 27 15 8 16), losses := [{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile31_node14 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,11] 2 profile31_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,11] 2 profile31_node14_cert).mp (by decide +kernel))

def profile31_node15_cert : CutBound 5 := { lost := (rows 8 0 8 0 0), upper := (rows 23 27 23 15 31), lower := (rows 23 27 23 8 16), losses := [{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile31_node15 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,19] 2 profile31_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,19] 2 profile31_node15_cert).mp (by decide +kernel))

def profile31_node16_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 23 27 29 15 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) }] }

theorem profile31_node16 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,25] 2 profile31_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,25] 2 profile31_node16_cert).mp (by decide +kernel))

def profile31_node17_cert : CutBound 5 := { lost := (rows 8 0 1 0 0), upper := (rows 23 27 30 15 23), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile31_node17 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,26] 2 profile31_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25,26] 2 profile31_node17_cert).mp (by decide +kernel))

def profile31_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node13 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25] 2 (by decide) (choices 3) [11,19,25,26] profile31_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,25] (choices 3) [11,19,25,26] profile31_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node14
  · exact profile31_node15
  · exact profile31_node16
  · exact profile31_node17

def profile31_node18_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 30 31 27 27), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile31_node18 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,28] 2 profile31_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22,28] 2 profile31_node18_cert).mp (by decide +kernel))

def profile31_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node7 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22] 2 (by decide) (choices 3) [13,21,25,28] profile31_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [22] (choices 3) [13,21,25,28] profile31_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node8
  · exact profile31_node12
  · exact profile31_node13
  · exact profile31_node18

def profile31_node20_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile31_node20 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,13] 2 profile31_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,13] 2 profile31_node20_cert).mp (by decide +kernel))

def profile31_node21_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 29 23 31 27 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile31_node21 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,21] 2 profile31_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,21] 2 profile31_node21_cert).mp (by decide +kernel))

def profile31_node22_cert : CutBound 5 := { lost := (rows 2 1 0 0 0), upper := (rows 29 30 23 27 19), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 4 8 16) }] }

theorem profile31_node22 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,28] 2 profile31_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28,28] 2 profile31_node22_cert).mp (by decide +kernel))

def profile31_node19_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile31_node19 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28] 2 (by decide) (choices 3) [13,21,28] profile31_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [28] (choices 3) [13,21,28] profile31_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node20
  · exact profile31_node21
  · exact profile31_node22

def profile31_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile31_node0 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [] 2 (by decide) (choices 3) [14,22,28] profile31_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [] (choices 3) [14,22,28] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node1
  · exact profile31_node7
  · exact profile31_node19

theorem profile31 : Upper (D (n:=5) [51,51,50,50,19]) (R (n:=5) [51,51,50,50,19]) [] 2 := profile31_node0

def profile32_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile32_node2 : Upper (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30,29] 2 profile32_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30,29] 2 profile32_node2_cert).mp (by decide +kernel))

def profile32_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node1 : Upper (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30] 2 (by decide) (choices 4) [29] profile32_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [30] (choices 4) [29] profile32_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node2

def profile32_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node0 : Upper (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [] 2 (by decide) (choices 4) [30] profile32_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [] (choices 4) [30] profile32_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node1

theorem profile32 : Upper (D (n:=5) [67,66,34,34,20]) (R (n:=5) [67,66,34,34,20]) [] 2 := profile32_node0

def profile33_node3_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 31 21 30 22), lower := (rows 31 31 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 21 8 16) }] }

theorem profile33_node3 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,17] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,17] 2 profile33_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,17] 2 profile33_node3_cert).mp (by decide +kernel))

def profile33_node4_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 31 22 29 21), lower := (rows 31 31 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile33_node4 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,18] 2 :=
  cut_bound_sound (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,18] 2 profile33_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29,18] 2 profile33_node4_cert).mp (by decide +kernel))

def profile33_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node2 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29] 2 (by decide) (choices 2) [17,18] profile33_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30,29] (choices 2) [17,18] profile33_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node3
  · exact profile33_node4

def profile33_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node1 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30] 2 (by decide) (choices 4) [29] profile33_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [30] (choices 4) [29] profile33_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node2

def profile33_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node0 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [] 2 (by decide) (choices 4) [30] profile33_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [] (choices 4) [30] profile33_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node1

theorem profile33 : Upper (D (n:=5) [66,66,35,34,20]) (R (n:=5) [66,66,35,34,20]) [] 2 := profile33_node0

def profile34_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile34_node2 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,21] 2 profile34_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,21] 2 profile34_node2_cert).mp (by decide +kernel))

def profile34_node3_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile34_node3 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,25] 2 profile34_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,25] 2 profile34_node3_cert).mp (by decide +kernel))

def profile34_node4_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile34_node4 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,28] 2 profile34_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30,28] 2 profile34_node4_cert).mp (by decide +kernel))

def profile34_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node1 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile34_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [30] (choices 3) [21,25,28] profile34_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node2
  · exact profile34_node3
  · exact profile34_node4

def profile34_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node0 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [] 2 (by decide) (choices 4) [30] profile34_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [] (choices 4) [30] profile34_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node1

theorem profile34 : Upper (D (n:=5) [67,50,50,34,20]) (R (n:=5) [67,50,50,34,20]) [] 2 := profile34_node0

def profile35_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile35_node2 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,21] 2 profile35_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,21] 2 profile35_node2_cert).mp (by decide +kernel))

def profile35_node3_cert : CutBound 5 := { lost := (rows 0 4 8 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile35_node3 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,25] 2 profile35_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,25] 2 profile35_node3_cert).mp (by decide +kernel))

def profile35_node4_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile35_node4 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,28] 2 profile35_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30,28] 2 profile35_node4_cert).mp (by decide +kernel))

def profile35_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node1 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile35_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [30] (choices 3) [21,25,28] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node2
  · exact profile35_node3
  · exact profile35_node4

def profile35_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node0 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [] 2 (by decide) (choices 4) [30] profile35_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [] (choices 4) [30] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=5) [66,51,50,34,20]) (R (n:=5) [66,51,50,34,20]) [] 2 := profile35_node0

def profile36_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile36_node2 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,21] 2 profile36_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,21] 2 profile36_node2_cert).mp (by decide +kernel))

def profile36_node4_cert : CutBound 5 := { lost := (rows 0 0 0 3 0), upper := (rows 31 27 23 28 28), lower := (rows 31 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile36_node4 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,19] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,19] 2 profile36_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,19] 2 profile36_node4_cert).mp (by decide +kernel))

def profile36_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 31 27 29 30 22), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile36_node5 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,25] 2 profile36_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,25] 2 profile36_node5_cert).mp (by decide +kernel))

def profile36_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 31 27 30 29 21), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) }] }

theorem profile36_node6 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,26] 2 profile36_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25,26] 2 profile36_node6_cert).mp (by decide +kernel))

def profile36_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node3 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25] 2 (by decide) (choices 3) [19,25,26] profile36_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,25] (choices 3) [19,25,26] profile36_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node4
  · exact profile36_node5
  · exact profile36_node6

def profile36_node7_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile36_node7 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,28] 2 profile36_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30,28] 2 profile36_node7_cert).mp (by decide +kernel))

def profile36_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile36_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [30] (choices 3) [21,25,28] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node2
  · exact profile36_node3
  · exact profile36_node7

def profile36_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node0 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [] 2 (by decide) (choices 4) [30] profile36_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [] (choices 4) [30] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node1

theorem profile36 : Upper (D (n:=5) [66,50,50,35,20]) (R (n:=5) [66,50,50,35,20]) [] 2 := profile36_node0

def profile37_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile37_node2 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,21] 2 profile37_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,21] 2 profile37_node2_cert).mp (by decide +kernel))

def profile37_node4_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 27 23 29 29), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile37_node4 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,19] 2 profile37_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,19] 2 profile37_node4_cert).mp (by decide +kernel))

def profile37_node5_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 23 27 29 31 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) }] }

theorem profile37_node5 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,25] 2 profile37_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,25] 2 profile37_node5_cert).mp (by decide +kernel))

def profile37_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 27 30 29 21), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) }] }

theorem profile37_node6 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,26] 2 profile37_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25,26] 2 profile37_node6_cert).mp (by decide +kernel))

def profile37_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node3 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25] 2 (by decide) (choices 3) [19,25,26] profile37_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,25] (choices 3) [19,25,26] profile37_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node4
  · exact profile37_node5
  · exact profile37_node6

def profile37_node7_cert : CutBound 5 := { lost := (rows 8 0 0 4 0), upper := (rows 23 30 31 27 27), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile37_node7 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,28] 2 profile37_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22,28] 2 profile37_node7_cert).mp (by decide +kernel))

def profile37_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22] 2 (by decide) (choices 3) [21,25,28] profile37_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [22] (choices 3) [21,25,28] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node2
  · exact profile37_node3
  · exact profile37_node7

def profile37_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile37_node0 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [] 2 (by decide) (choices 3) [22] profile37_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [] (choices 3) [22] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=5) [51,50,50,50,20]) (R (n:=5) [51,50,50,50,20]) [] 2 := profile37_node0

def profile38_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 15 7 11 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile38_node2 : Upper (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30,13] 2 profile38_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30,13] 2 profile38_node2_cert).mp (by decide +kernel))

def profile38_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30] 2 (by decide) (choices 3) [13] profile38_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [30] (choices 3) [13] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node2

def profile38_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node0 : Upper (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [] 2 (by decide) (choices 4) [30] profile38_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [] (choices 4) [30] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node1

theorem profile38 : Upper (D (n:=5) [68,52,34,34,33]) (R (n:=5) [68,52,34,34,33]) [] 2 := profile38_node0

def profile39_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile39_node2 : Upper (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30,13] 2 profile39_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30,13] 2 profile39_node2_cert).mp (by decide +kernel))

def profile39_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node1 : Upper (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30] 2 (by decide) (choices 3) [13] profile39_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [30] (choices 3) [13] profile39_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node2

def profile39_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node0 : Upper (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [] 2 (by decide) (choices 4) [30] profile39_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [] (choices 4) [30] profile39_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node1

theorem profile39 : Upper (D (n:=5) [68,51,35,34,33]) (R (n:=5) [68,51,35,34,33]) [] 2 := profile39_node0

def profile40_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile40_node2 : Upper (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30,13] 2 profile40_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30,13] 2 profile40_node2_cert).mp (by decide +kernel))

def profile40_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node1 : Upper (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30] 2 (by decide) (choices 3) [13] profile40_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [30] (choices 3) [13] profile40_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node2

def profile40_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node0 : Upper (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [] 2 (by decide) (choices 4) [30] profile40_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [] (choices 4) [30] profile40_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node1

theorem profile40 : Upper (D (n:=5) [67,52,35,34,33]) (R (n:=5) [67,52,35,34,33]) [] 2 := profile40_node0

def profile41_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile41_node2 : Upper (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30,13] 2 profile41_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30,13] 2 profile41_node2_cert).mp (by decide +kernel))

def profile41_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node1 : Upper (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30] 2 (by decide) (choices 3) [13] profile41_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [30] (choices 3) [13] profile41_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node2

def profile41_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node0 : Upper (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [] 2 (by decide) (choices 4) [30] profile41_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [] (choices 4) [30] profile41_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node1

theorem profile41 : Upper (D (n:=5) [68,50,36,34,33]) (R (n:=5) [68,50,36,34,33]) [] 2 := profile41_node0

def profile42_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile42_node2 : Upper (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30,13] 2 profile42_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30,13] 2 profile42_node2_cert).mp (by decide +kernel))

def profile42_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node1 : Upper (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30] 2 (by decide) (choices 3) [13] profile42_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [30] (choices 3) [13] profile42_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node2

def profile42_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node0 : Upper (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [] 2 (by decide) (choices 4) [30] profile42_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [] (choices 4) [30] profile42_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=5) [67,51,36,34,33]) (R (n:=5) [67,51,36,34,33]) [] 2 := profile42_node0

def profile43_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile43_node2 : Upper (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30,13] 2 profile43_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30,13] 2 profile43_node2_cert).mp (by decide +kernel))

def profile43_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node1 : Upper (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30] 2 (by decide) (choices 3) [13] profile43_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [30] (choices 3) [13] profile43_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node2

def profile43_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node0 : Upper (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [] 2 (by decide) (choices 4) [30] profile43_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [] (choices 4) [30] profile43_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node1

theorem profile43 : Upper (D (n:=5) [66,52,36,34,33]) (R (n:=5) [66,52,36,34,33]) [] 2 := profile43_node0

def profile44_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile44_node2 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,13] 2 profile44_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,13] 2 profile44_node2_cert).mp (by decide +kernel))

def profile44_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 23 15 11 27), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile44_node3 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,21] 2 profile44_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,21] 2 profile44_node3_cert).mp (by decide +kernel))

def profile44_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 27 7 15 23), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile44_node4 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,25] 2 profile44_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14,25] 2 profile44_node4_cert).mp (by decide +kernel))

def profile44_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node1 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14] 2 (by decide) (choices 3) [13,21,25] profile44_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [14] (choices 3) [13,21,25] profile44_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile44_node2
  · exact profile44_node3
  · exact profile44_node4

def profile44_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 23 15 15 11 27), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile44_node6 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22,13] 2 profile44_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22,13] 2 profile44_node6_cert).mp (by decide +kernel))

def profile44_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node5 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22] 2 (by decide) (choices 3) [13] profile44_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [22] (choices 3) [13] profile44_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node6

def profile44_node8_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 27 15 7 15 23), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile44_node8 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26,13] 2 profile44_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26,13] 2 profile44_node8_cert).mp (by decide +kernel))

def profile44_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node7 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26] 2 (by decide) (choices 3) [13] profile44_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [26] (choices 3) [13] profile44_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node8

def profile44_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node0 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [] 2 (by decide) (choices 3) [14,22,26] profile44_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [] (choices 3) [14,22,26] profile44_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile44_node1
  · exact profile44_node5
  · exact profile44_node7

theorem profile44 : Upper (D (n:=5) [52,52,50,34,33]) (R (n:=5) [52,52,50,34,33]) [] 2 := profile44_node0

def profile45_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 15 23 31 23), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile45_node2 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,13] 2 profile45_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,13] 2 profile45_node2_cert).mp (by decide +kernel))

def profile45_node4_cert : CutBound 5 := { lost := (rows 0 8 0 0 8), upper := (rows 15 23 15 15 23), lower := (rows 15 23 15 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile45_node4 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21,11] 2 profile45_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21,11] 2 profile45_node4_cert).mp (by decide +kernel))

def profile45_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node3 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21] 2 (by decide) (choices 3) [11] profile45_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,21] (choices 3) [11] profile45_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node4

def profile45_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 27 7 15 23), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile45_node5 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,25] 2 profile45_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14,25] 2 profile45_node5_cert).mp (by decide +kernel))

def profile45_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node1 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14] 2 (by decide) (choices 3) [13,21,25] profile45_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [14] (choices 3) [13,21,25] profile45_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile45_node2
  · exact profile45_node3
  · exact profile45_node5

def profile45_node8_cert : CutBound 5 := { lost := (rows 8 0 0 0 8), upper := (rows 23 15 15 15 23), lower := (rows 23 15 15 8 16), losses := [{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile45_node8 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13,11] 2 profile45_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13,11] 2 profile45_node8_cert).mp (by decide +kernel))

def profile45_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node7 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13] 2 (by decide) (choices 3) [11] profile45_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22,13] (choices 3) [11] profile45_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node8

def profile45_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node6 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22] 2 (by decide) (choices 3) [13] profile45_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [22] (choices 3) [13] profile45_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node7

def profile45_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 27 15 7 15 23), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile45_node10 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26,13] 2 profile45_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26,13] 2 profile45_node10_cert).mp (by decide +kernel))

def profile45_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node9 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26] 2 (by decide) (choices 3) [13] profile45_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [26] (choices 3) [13] profile45_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node10

def profile45_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile45_node0 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [] 2 (by decide) (choices 3) [14,22,26] profile45_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [] (choices 3) [14,22,26] profile45_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile45_node1
  · exact profile45_node6
  · exact profile45_node9

theorem profile45 : Upper (D (n:=5) [52,51,51,34,33]) (R (n:=5) [52,51,51,34,33]) [] 2 := profile45_node0

def profile46_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 15 7 13 29), lower := (rows 31 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile46_node3 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,3] 2 profile46_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,3] 2 profile46_node3_cert).mp (by decide +kernel))

def profile46_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 13 15 23), lower := (rows 31 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile46_node4 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,9] 2 profile46_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13,9] 2 profile46_node4_cert).mp (by decide +kernel))

def profile46_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node2 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13] 2 (by decide) (choices 2) [3,9] profile46_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30,13] (choices 2) [3,9] profile46_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile46_node3
  · exact profile46_node4

def profile46_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node1 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30] 2 (by decide) (choices 3) [13] profile46_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [30] (choices 3) [13] profile46_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node2

def profile46_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node0 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [] 2 (by decide) (choices 4) [30] profile46_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [] (choices 4) [30] profile46_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node1

theorem profile46 : Upper (D (n:=5) [68,50,35,35,33]) (R (n:=5) [68,50,35,35,33]) [] 2 := profile46_node0

def profile47_node4_cert : CutBound 5 := { lost := (rows 0 0 0 0 3), upper := (rows 31 15 7 11 28), lower := (rows 31 15 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 25 16) }] }

theorem profile47_node4 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,3] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,3] 2 profile47_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,3] 2 profile47_node4_cert).mp (by decide +kernel))

def profile47_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 1), upper := (rows 31 15 7 13 26), lower := (rows 31 15 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) }] }

theorem profile47_node5 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,5] 2 profile47_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,5] 2 profile47_node5_cert).mp (by decide +kernel))

def profile47_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 2), upper := (rows 31 15 7 14 25), lower := (rows 31 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 28 16) }] }

theorem profile47_node6 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,6] 2 profile47_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3,6] 2 profile47_node6_cert).mp (by decide +kernel))

def profile47_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node3 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3] 2 (by decide) (choices 2) [3,5,6] profile47_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,3] (choices 2) [3,5,6] profile47_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile47_node4
  · exact profile47_node5
  · exact profile47_node6

def profile47_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 13 15 23), lower := (rows 31 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile47_node7 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,9] 2 profile47_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,9] 2 profile47_node7_cert).mp (by decide +kernel))

def profile47_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 14 15 23), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile47_node8 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,10] 2 profile47_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13,10] 2 profile47_node8_cert).mp (by decide +kernel))

def profile47_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node2 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13] 2 (by decide) (choices 2) [3,9,10] profile47_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30,13] (choices 2) [3,9,10] profile47_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile47_node3
  · exact profile47_node7
  · exact profile47_node8

def profile47_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node1 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30] 2 (by decide) (choices 3) [13] profile47_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [30] (choices 3) [13] profile47_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node2

def profile47_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node0 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [] 2 (by decide) (choices 4) [30] profile47_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [] (choices 4) [30] profile47_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node1

theorem profile47 : Upper (D (n:=5) [67,51,35,35,33]) (R (n:=5) [67,51,35,35,33]) [] 2 := profile47_node0

def profile48_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 7 14 30), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile48_node3 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,3] 2 profile48_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,3] 2 profile48_node3_cert).mp (by decide +kernel))

def profile48_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 14 15 23), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile48_node4 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,10] 2 profile48_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13,10] 2 profile48_node4_cert).mp (by decide +kernel))

def profile48_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node2 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13] 2 (by decide) (choices 2) [3,10] profile48_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30,13] (choices 2) [3,10] profile48_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile48_node3
  · exact profile48_node4

def profile48_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node1 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30] 2 (by decide) (choices 3) [13] profile48_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [30] (choices 3) [13] profile48_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node2

def profile48_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node0 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [] 2 (by decide) (choices 4) [30] profile48_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [] (choices 4) [30] profile48_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node1

theorem profile48 : Upper (D (n:=5) [66,52,35,35,33]) (R (n:=5) [66,52,35,35,33]) [] 2 := profile48_node0

def profile49_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 15 7 13 29), lower := (rows 31 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile49_node3 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,3] 2 profile49_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,3] 2 profile49_node3_cert).mp (by decide +kernel))

def profile49_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 8), upper := (rows 31 15 13 15 23), lower := (rows 31 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile49_node4 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,9] 2 profile49_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,9] 2 profile49_node4_cert).mp (by decide +kernel))

def profile49_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 31 15 14 13 21), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile49_node5 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,10] 2 profile49_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13,10] 2 profile49_node5_cert).mp (by decide +kernel))

def profile49_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node2 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13] 2 (by decide) (choices 2) [3,9,10] profile49_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30,13] (choices 2) [3,9,10] profile49_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node3
  · exact profile49_node4
  · exact profile49_node5

def profile49_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node1 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30] 2 (by decide) (choices 3) [13] profile49_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [30] (choices 3) [13] profile49_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node2

def profile49_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node0 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [] 2 (by decide) (choices 4) [30] profile49_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [] (choices 4) [30] profile49_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node1

theorem profile49 : Upper (D (n:=5) [67,50,36,35,33]) (R (n:=5) [67,50,36,35,33]) [] 2 := profile49_node0

def profile50_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 7 14 30), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile50_node3 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,3] 2 profile50_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,3] 2 profile50_node3_cert).mp (by decide +kernel))

def profile50_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 13 14 22), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile50_node4 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,9] 2 profile50_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,9] 2 profile50_node4_cert).mp (by decide +kernel))

def profile50_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 8), upper := (rows 31 15 14 15 23), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile50_node5 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,10] 2 profile50_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13,10] 2 profile50_node5_cert).mp (by decide +kernel))

def profile50_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node2 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13] 2 (by decide) (choices 2) [3,9,10] profile50_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30,13] (choices 2) [3,9,10] profile50_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile50_node3
  · exact profile50_node4
  · exact profile50_node5

def profile50_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node1 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30] 2 (by decide) (choices 3) [13] profile50_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [30] (choices 3) [13] profile50_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node2

def profile50_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node0 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [] 2 (by decide) (choices 4) [30] profile50_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [] (choices 4) [30] profile50_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node1

theorem profile50 : Upper (D (n:=5) [66,51,36,35,33]) (R (n:=5) [66,51,36,35,33]) [] 2 := profile50_node0

#print axioms profile50
end Delivery.FiveVertexPositive13
