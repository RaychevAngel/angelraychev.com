import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile39_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile39_node2 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14,21] 2 profile39_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14,21] 2 profile39_node2_cert).mp (by decide +kernel))

def profile39_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node1 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14] 2 (by decide) (choices 3) [21] profile39_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [14] (choices 3) [21] profile39_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node2

def profile39_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile39_node4 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,13] 2 profile39_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,13] 2 profile39_node4_cert).mp (by decide +kernel))

def profile39_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile39_node5 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,21] 2 profile39_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,21] 2 profile39_node5_cert).mp (by decide +kernel))

def profile39_node7_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 27 23 15 23), lower := (rows 23 27 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile39_node7 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25,19] 2 profile39_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25,19] 2 profile39_node7_cert).mp (by decide +kernel))

def profile39_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node6 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25] 2 (by decide) (choices 3) [19] profile39_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,25] (choices 3) [19] profile39_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node7

def profile39_node8_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 23 27 19), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile39_node8 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,28] 2 profile39_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22,28] 2 profile39_node8_cert).mp (by decide +kernel))

def profile39_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node3 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22] 2 (by decide) (choices 3) [13,21,25,28] profile39_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [22] (choices 3) [13,21,25,28] profile39_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile39_node4
  · exact profile39_node5
  · exact profile39_node6
  · exact profile39_node8

def profile39_node11_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 27 23 23 15 23), lower := (rows 27 23 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile39_node11 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21,19] 2 profile39_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21,19] 2 profile39_node11_cert).mp (by decide +kernel))

def profile39_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node10 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21] 2 (by decide) (choices 3) [19] profile39_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26,21] (choices 3) [19] profile39_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node11

def profile39_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node9 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26] 2 (by decide) (choices 3) [21] profile39_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [26] (choices 3) [21] profile39_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node10

def profile39_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 23 27 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile39_node13 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28,21] 2 profile39_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28,21] 2 profile39_node13_cert).mp (by decide +kernel))

def profile39_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node12 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28] 2 (by decide) (choices 3) [21] profile39_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [28] (choices 3) [21] profile39_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node13

def profile39_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node0 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [] 2 (by decide) (choices 3) [14,22,26,28] profile39_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [] (choices 3) [14,22,26,28] profile39_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile39_node1
  · exact profile39_node3
  · exact profile39_node9
  · exact profile39_node12

theorem profile39 : Upper (D (n:=5) [51,51,50,33,19]) (R (n:=5) [51,51,50,33,19]) [] 2 := profile39_node0

def profile40_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 15 21 25 17), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile40_node2 : Upper (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,13] 2 profile40_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,13] 2 profile40_node2_cert).mp (by decide +kernel))

def profile40_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 29 25 25), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile40_node3 : Upper (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,21] 2 profile40_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30,21] 2 profile40_node3_cert).mp (by decide +kernel))

def profile40_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile40_node1 : Upper (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30] 2 (by decide) (choices 3) [13,21] profile40_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [30] (choices 3) [13,21] profile40_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node2
  · exact profile40_node3

def profile40_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node0 : Upper (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [] 2 (by decide) (choices 4) [30] profile40_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [] (choices 4) [30] profile40_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node1

theorem profile40 : Upper (D (n:=5) [68,49,34,34,19]) (R (n:=5) [68,49,34,34,19]) [] 2 := profile40_node0

def profile41_node2_cert : CutBound 5 := { lost := (rows 0 16 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile41_node2 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,13] 2 profile41_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,13] 2 profile41_node2_cert).mp (by decide +kernel))

def profile41_node4_cert : CutBound 5 := { lost := (rows 0 8 8 6 0), upper := (rows 31 23 7 25 25), lower := (rows 31 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile41_node4 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,3] 2 profile41_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,3] 2 profile41_node4_cert).mp (by decide +kernel))

def profile41_node5_cert : CutBound 5 := { lost := (rows 0 8 2 4 0), upper := (rows 31 23 13 27 19), lower := (rows 31 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile41_node5 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,9] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,9] 2 profile41_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,9] 2 profile41_node5_cert).mp (by decide +kernel))

def profile41_node6_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 31 23 14 25 17), lower := (rows 31 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile41_node6 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,10] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,10] 2 profile41_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,10] 2 profile41_node6_cert).mp (by decide +kernel))

def profile41_node7_cert : CutBound 5 := { lost := (rows 0 8 10 4 0), upper := (rows 31 23 21 11 27), lower := (rows 31 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile41_node7 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,17] 2 profile41_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,17] 2 profile41_node7_cert).mp (by decide +kernel))

def profile41_node8_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 31 23 22 9 25), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile41_node8 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,18] 2 profile41_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,18] 2 profile41_node8_cert).mp (by decide +kernel))

def profile41_node9_cert : CutBound 5 := { lost := (rows 0 0 3 4 0), upper := (rows 31 23 28 11 19), lower := (rows 31 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) }] }

theorem profile41_node9 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,24] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,24] 2 profile41_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21,24] 2 profile41_node9_cert).mp (by decide +kernel))

def profile41_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node3 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile41_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,21] (choices 2) [3,9,10,17,18,24] profile41_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node4
  · exact profile41_node5
  · exact profile41_node6
  · exact profile41_node7
  · exact profile41_node8
  · exact profile41_node9

def profile41_node10_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile41_node10 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,28] 2 profile41_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30,28] 2 profile41_node10_cert).mp (by decide +kernel))

def profile41_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile41_node1 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile41_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [30] (choices 3) [13,21,28] profile41_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile41_node2
  · exact profile41_node3
  · exact profile41_node10

def profile41_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node0 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [] 2 (by decide) (choices 4) [30] profile41_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [] (choices 4) [30] profile41_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node1

theorem profile41 : Upper (D (n:=5) [67,50,34,34,19]) (R (n:=5) [67,50,34,34,19]) [] 2 := profile41_node0

def profile42_node2_cert : CutBound 5 := { lost := (rows 0 16 8 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile42_node2 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,13] 2 profile42_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,13] 2 profile42_node2_cert).mp (by decide +kernel))

def profile42_node4_cert : CutBound 5 := { lost := (rows 0 8 8 5 0), upper := (rows 31 23 7 26 26), lower := (rows 31 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile42_node4 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,3] 2 profile42_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,3] 2 profile42_node4_cert).mp (by decide +kernel))

def profile42_node5_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 31 23 13 26 18), lower := (rows 31 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile42_node5 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,9] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,9] 2 profile42_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,9] 2 profile42_node5_cert).mp (by decide +kernel))

def profile42_node6_cert : CutBound 5 := { lost := (rows 0 8 1 4 0), upper := (rows 31 23 14 27 19), lower := (rows 31 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile42_node6 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,10] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,10] 2 profile42_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,10] 2 profile42_node6_cert).mp (by decide +kernel))

def profile42_node7_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 31 23 21 10 26), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile42_node7 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,17] 2 profile42_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,17] 2 profile42_node7_cert).mp (by decide +kernel))

def profile42_node8_cert : CutBound 5 := { lost := (rows 0 8 9 4 0), upper := (rows 31 23 22 11 27), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 22 0 16) }] }

theorem profile42_node8 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,18] 2 profile42_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,18] 2 profile42_node8_cert).mp (by decide +kernel))

def profile42_node9_cert : CutBound 5 := { lost := (rows 0 0 3 4 0), upper := (rows 31 23 28 11 19), lower := (rows 31 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) }] }

theorem profile42_node9 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,24] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,24] 2 profile42_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21,24] 2 profile42_node9_cert).mp (by decide +kernel))

def profile42_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node3 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile42_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,21] (choices 2) [3,9,10,17,18,24] profile42_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile42_node4
  · exact profile42_node5
  · exact profile42_node6
  · exact profile42_node7
  · exact profile42_node8
  · exact profile42_node9

def profile42_node10_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile42_node10 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,28] 2 profile42_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30,28] 2 profile42_node10_cert).mp (by decide +kernel))

def profile42_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile42_node1 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile42_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [30] (choices 3) [13,21,28] profile42_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node2
  · exact profile42_node3
  · exact profile42_node10

def profile42_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node0 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [] 2 (by decide) (choices 4) [30] profile42_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [] (choices 4) [30] profile42_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=5) [66,51,34,34,19]) (R (n:=5) [66,51,34,34,19]) [] 2 := profile42_node0

def profile43_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 15 22 26 18), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile43_node2 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,13] 2 profile43_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,13] 2 profile43_node2_cert).mp (by decide +kernel))

def profile43_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 30 26 26), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile43_node3 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,21] 2 profile43_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,21] 2 profile43_node3_cert).mp (by decide +kernel))

def profile43_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile43_node4 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,28] 2 profile43_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30,28] 2 profile43_node4_cert).mp (by decide +kernel))

def profile43_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile43_node1 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile43_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [30] (choices 3) [13,21,28] profile43_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node2
  · exact profile43_node3
  · exact profile43_node4

def profile43_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node0 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [] 2 (by decide) (choices 4) [30] profile43_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [] (choices 4) [30] profile43_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node1

theorem profile43 : Upper (D (n:=5) [65,52,34,34,19]) (R (n:=5) [65,52,34,34,19]) [] 2 := profile43_node0

def profile44_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 21 29 21), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile44_node2 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,13] 2 profile44_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,13] 2 profile44_node2_cert).mp (by decide +kernel))

def profile44_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 29 29 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile44_node3 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,21] 2 profile44_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,21] 2 profile44_node3_cert).mp (by decide +kernel))

def profile44_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 21 29 21), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile44_node4 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,25] 2 profile44_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,25] 2 profile44_node4_cert).mp (by decide +kernel))

def profile44_node5_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 21 29 21), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile44_node5 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,28] 2 profile44_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30,28] 2 profile44_node5_cert).mp (by decide +kernel))

def profile44_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node1 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile44_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [30] (choices 3) [13,21,25,28] profile44_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile44_node2
  · exact profile44_node3
  · exact profile44_node4
  · exact profile44_node5

def profile44_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node0 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [] 2 (by decide) (choices 4) [30] profile44_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [] (choices 4) [30] profile44_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node1

theorem profile44 : Upper (D (n:=5) [67,49,35,34,19]) (R (n:=5) [67,49,35,34,19]) [] 2 := profile44_node0

def profile45_node3_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 31 15 21 30 22), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile45_node3 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,17] 2 profile45_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,17] 2 profile45_node3_cert).mp (by decide +kernel))

def profile45_node4_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 31 15 22 29 21), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile45_node4 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,18] 2 profile45_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13,18] 2 profile45_node4_cert).mp (by decide +kernel))

def profile45_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node2 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13] 2 (by decide) (choices 2) [17,18] profile45_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,13] (choices 2) [17,18] profile45_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile45_node3
  · exact profile45_node4

def profile45_node6_cert : CutBound 5 := { lost := (rows 0 8 8 3 0), upper := (rows 31 23 7 28 28), lower := (rows 31 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile45_node6 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,3] 2 profile45_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,3] 2 profile45_node6_cert).mp (by decide +kernel))

def profile45_node7_cert : CutBound 5 := { lost := (rows 0 8 2 1 0), upper := (rows 31 23 13 30 22), lower := (rows 31 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile45_node7 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,9] 2 profile45_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,9] 2 profile45_node7_cert).mp (by decide +kernel))

def profile45_node8_cert : CutBound 5 := { lost := (rows 0 8 1 2 0), upper := (rows 31 23 14 29 21), lower := (rows 31 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile45_node8 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,10] 2 profile45_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,10] 2 profile45_node8_cert).mp (by decide +kernel))

def profile45_node9_cert : CutBound 5 := { lost := (rows 0 8 10 1 0), upper := (rows 31 23 21 14 30), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile45_node9 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,17] 2 profile45_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,17] 2 profile45_node9_cert).mp (by decide +kernel))

def profile45_node10_cert : CutBound 5 := { lost := (rows 0 8 9 2 0), upper := (rows 31 23 22 13 29), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 22 0 16) }] }

theorem profile45_node10 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,18] 2 profile45_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,18] 2 profile45_node10_cert).mp (by decide +kernel))

def profile45_node11_cert : CutBound 5 := { lost := (rows 0 8 3 0 0), upper := (rows 31 23 28 15 23), lower := (rows 31 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile45_node11 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,24] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,24] 2 profile45_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21,24] 2 profile45_node11_cert).mp (by decide +kernel))

def profile45_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node5 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile45_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,21] (choices 2) [3,9,10,17,18,24] profile45_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile45_node6
  · exact profile45_node7
  · exact profile45_node8
  · exact profile45_node9
  · exact profile45_node10
  · exact profile45_node11

def profile45_node13_cert : CutBound 5 := { lost := (rows 0 4 0 3 0), upper := (rows 31 27 7 28 20), lower := (rows 31 27 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 3 8 16) }] }

theorem profile45_node13 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,3] 2 profile45_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,3] 2 profile45_node13_cert).mp (by decide +kernel))

def profile45_node14_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 31 27 21 14 22), lower := (rows 31 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 21 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 19 8 16) }] }

theorem profile45_node14 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,17] 2 profile45_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,17] 2 profile45_node14_cert).mp (by decide +kernel))

def profile45_node15_cert : CutBound 5 := { lost := (rows 0 4 1 2 0), upper := (rows 31 27 22 13 21), lower := (rows 31 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 18 8 16) }] }

theorem profile45_node15 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,18] 2 profile45_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25,18] 2 profile45_node15_cert).mp (by decide +kernel))

def profile45_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node12 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25] 2 (by decide) (choices 2) [3,17,18] profile45_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,25] (choices 2) [3,17,18] profile45_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile45_node13
  · exact profile45_node14
  · exact profile45_node15

def profile45_node17_cert : CutBound 5 := { lost := (rows 0 1 8 2 0), upper := (rows 31 30 7 29 21), lower := (rows 31 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile45_node17 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,3] 2 profile45_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,3] 2 profile45_node17_cert).mp (by decide +kernel))

def profile45_node18_cert : CutBound 5 := { lost := (rows 0 1 10 0 0), upper := (rows 31 30 21 15 23), lower := (rows 31 30 21 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 21 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 21 0 16) }] }

theorem profile45_node18 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,17] 2 profile45_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,17] 2 profile45_node18_cert).mp (by decide +kernel))

def profile45_node19_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 31 30 22 13 21), lower := (rows 31 30 22 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) }] }

theorem profile45_node19 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,18] 2 profile45_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28,18] 2 profile45_node19_cert).mp (by decide +kernel))

def profile45_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node16 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28] 2 (by decide) (choices 2) [3,17,18] profile45_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30,28] (choices 2) [3,17,18] profile45_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile45_node17
  · exact profile45_node18
  · exact profile45_node19

def profile45_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node1 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile45_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [30] (choices 3) [13,21,25,28] profile45_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile45_node2
  · exact profile45_node5
  · exact profile45_node12
  · exact profile45_node16

def profile45_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node0 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [] 2 (by decide) (choices 4) [30] profile45_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [] (choices 4) [30] profile45_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node1

theorem profile45 : Upper (D (n:=5) [66,50,35,34,19]) (R (n:=5) [66,50,35,34,19]) [] 2 := profile45_node0

def profile46_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 22 30 22), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile46_node2 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,13] 2 profile46_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,13] 2 profile46_node2_cert).mp (by decide +kernel))

def profile46_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 30 30 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile46_node3 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,21] 2 profile46_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,21] 2 profile46_node3_cert).mp (by decide +kernel))

def profile46_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 22 30 22), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile46_node4 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,25] 2 profile46_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,25] 2 profile46_node4_cert).mp (by decide +kernel))

def profile46_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile46_node5 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,28] 2 profile46_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30,28] 2 profile46_node5_cert).mp (by decide +kernel))

def profile46_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node1 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile46_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [30] (choices 3) [13,21,25,28] profile46_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile46_node2
  · exact profile46_node3
  · exact profile46_node4
  · exact profile46_node5

def profile46_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node0 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [] 2 (by decide) (choices 4) [30] profile46_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [] (choices 4) [30] profile46_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node1

theorem profile46 : Upper (D (n:=5) [65,51,35,34,19]) (R (n:=5) [65,51,35,34,19]) [] 2 := profile46_node0

def profile47_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 21 29 21), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile47_node2 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,13] 2 profile47_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,13] 2 profile47_node2_cert).mp (by decide +kernel))

def profile47_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 29 29 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile47_node3 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,21] 2 profile47_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,21] 2 profile47_node3_cert).mp (by decide +kernel))

def profile47_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 21 29 21), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile47_node4 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,28] 2 profile47_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30,28] 2 profile47_node4_cert).mp (by decide +kernel))

def profile47_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node1 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile47_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [30] (choices 3) [13,21,28] profile47_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile47_node2
  · exact profile47_node3
  · exact profile47_node4

def profile47_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node0 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [] 2 (by decide) (choices 4) [30] profile47_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [] (choices 4) [30] profile47_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node1

theorem profile47 : Upper (D (n:=5) [66,49,36,34,19]) (R (n:=5) [66,49,36,34,19]) [] 2 := profile47_node0

def profile48_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 22 30 22), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile48_node2 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,13] 2 profile48_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,13] 2 profile48_node2_cert).mp (by decide +kernel))

def profile48_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 30 30 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile48_node3 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,21] 2 profile48_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,21] 2 profile48_node3_cert).mp (by decide +kernel))

def profile48_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile48_node4 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,28] 2 profile48_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30,28] 2 profile48_node4_cert).mp (by decide +kernel))

def profile48_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node1 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile48_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [30] (choices 3) [13,21,28] profile48_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile48_node2
  · exact profile48_node3
  · exact profile48_node4

def profile48_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node0 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [] 2 (by decide) (choices 4) [30] profile48_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [] (choices 4) [30] profile48_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node1

theorem profile48 : Upper (D (n:=5) [65,50,36,34,19]) (R (n:=5) [65,50,36,34,19]) [] 2 := profile48_node0

def profile49_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 23 27 19), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile49_node2 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14,25] 2 profile49_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14,25] 2 profile49_node2_cert).mp (by decide +kernel))

def profile49_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node1 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14] 2 (by decide) (choices 3) [25] profile49_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [14] (choices 3) [25] profile49_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node2

def profile49_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 15 25 17), lower := (rows 23 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile49_node5 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,11] 2 profile49_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,11] 2 profile49_node5_cert).mp (by decide +kernel))

def profile49_node6_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 23 9 25), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile49_node6 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,19] 2 profile49_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,19] 2 profile49_node6_cert).mp (by decide +kernel))

def profile49_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 27 29 11 19), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) }] }

theorem profile49_node7 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,25] 2 profile49_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25,25] 2 profile49_node7_cert).mp (by decide +kernel))

def profile49_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node4 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25] 2 (by decide) (choices 3) [11,19,25] profile49_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22,25] (choices 3) [11,19,25] profile49_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node5
  · exact profile49_node6
  · exact profile49_node7

def profile49_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node3 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22] 2 (by decide) (choices 3) [25] profile49_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [22] (choices 3) [25] profile49_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node4

def profile49_node9_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 23 27 19), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile49_node9 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,13] 2 profile49_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,13] 2 profile49_node9_cert).mp (by decide +kernel))

def profile49_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 15 25 17), lower := (rows 27 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile49_node11 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,11] 2 profile49_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,11] 2 profile49_node11_cert).mp (by decide +kernel))

def profile49_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 23 9 25), lower := (rows 27 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile49_node12 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,19] 2 profile49_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,19] 2 profile49_node12_cert).mp (by decide +kernel))

def profile49_node13_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 23 29 11 19), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile49_node13 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,25] 2 profile49_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21,25] 2 profile49_node13_cert).mp (by decide +kernel))

def profile49_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node10 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21] 2 (by decide) (choices 3) [11,19,25] profile49_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,21] (choices 3) [11,19,25] profile49_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node11
  · exact profile49_node12
  · exact profile49_node13

def profile49_node14_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 27 23 31 23), lower := (rows 27 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile49_node14 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,25] 2 profile49_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26,25] 2 profile49_node14_cert).mp (by decide +kernel))

def profile49_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node8 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26] 2 (by decide) (choices 3) [13,21,25] profile49_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [26] (choices 3) [13,21,25] profile49_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile49_node9
  · exact profile49_node10
  · exact profile49_node14

def profile49_node16_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 27 23 27 19), lower := (rows 29 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile49_node16 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28,25] 2 profile49_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28,25] 2 profile49_node16_cert).mp (by decide +kernel))

def profile49_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node15 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28] 2 (by decide) (choices 3) [25] profile49_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [28] (choices 3) [25] profile49_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node16

def profile49_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node0 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [] 2 (by decide) (choices 3) [14,22,26,28] profile49_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [] (choices 3) [14,22,26,28] profile49_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile49_node1
  · exact profile49_node3
  · exact profile49_node8
  · exact profile49_node15

theorem profile49 : Upper (D (n:=5) [52,50,49,34,19]) (R (n:=5) [52,50,49,34,19]) [] 2 := profile49_node0

def profile50_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 23 27 19), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile50_node2 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14,25] 2 profile50_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14,25] 2 profile50_node2_cert).mp (by decide +kernel))

def profile50_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node1 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14] 2 (by decide) (choices 3) [25] profile50_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [14] (choices 3) [25] profile50_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node2

def profile50_node5_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 27 15 27 19), lower := (rows 23 27 15 8 16), losses := [{ target := 3, region := (rows 5 2 4 0 23), good := (rows 23 19 23 0 16) }] }

theorem profile50_node5 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,11] 2 profile50_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,11] 2 profile50_node5_cert).mp (by decide +kernel))

def profile50_node6_cert : CutBound 5 := { lost := (rows 8 0 8 0 0), upper := (rows 23 27 23 11 27), lower := (rows 23 27 23 8 16), losses := [{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile50_node6 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,19] 2 profile50_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,19] 2 profile50_node6_cert).mp (by decide +kernel))

def profile50_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 27 29 11 19), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) }] }

theorem profile50_node7 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,25] 2 profile50_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,25] 2 profile50_node7_cert).mp (by decide +kernel))

def profile50_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 30 11 19), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) }] }

theorem profile50_node8 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,26] 2 profile50_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25,26] 2 profile50_node8_cert).mp (by decide +kernel))

def profile50_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node4 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25] 2 (by decide) (choices 3) [11,19,25,26] profile50_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22,25] (choices 3) [11,19,25,26] profile50_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile50_node5
  · exact profile50_node6
  · exact profile50_node7
  · exact profile50_node8

def profile50_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node3 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22] 2 (by decide) (choices 3) [25] profile50_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [22] (choices 3) [25] profile50_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node4

def profile50_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 23 27 19), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile50_node10 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,13] 2 profile50_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,13] 2 profile50_node10_cert).mp (by decide +kernel))

def profile50_node12_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 27 23 15 27 19), lower := (rows 27 23 15 8 16), losses := [{ target := 3, region := (rows 1 6 4 0 23), good := (rows 19 23 23 0 16) }] }

theorem profile50_node12 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,11] 2 profile50_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,11] 2 profile50_node12_cert).mp (by decide +kernel))

def profile50_node13_cert : CutBound 5 := { lost := (rows 0 8 8 0 0), upper := (rows 27 23 23 11 27), lower := (rows 27 23 23 8 16), losses := [{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile50_node13 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,19] 2 profile50_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,19] 2 profile50_node13_cert).mp (by decide +kernel))

def profile50_node14_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 23 29 11 19), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile50_node14 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,25] 2 profile50_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,25] 2 profile50_node14_cert).mp (by decide +kernel))

def profile50_node15_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 30 11 19), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) }] }

theorem profile50_node15 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,26] 2 profile50_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21,26] 2 profile50_node15_cert).mp (by decide +kernel))

def profile50_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node11 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21] 2 (by decide) (choices 3) [11,19,25,26] profile50_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,21] (choices 3) [11,19,25,26] profile50_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile50_node12
  · exact profile50_node13
  · exact profile50_node14
  · exact profile50_node15

def profile50_node16_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 27 23 31 23), lower := (rows 27 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile50_node16 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,25] 2 profile50_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,25] 2 profile50_node16_cert).mp (by decide +kernel))

def profile50_node17_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 30 23 27 19), lower := (rows 27 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile50_node17 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,28] 2 profile50_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26,28] 2 profile50_node17_cert).mp (by decide +kernel))

def profile50_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node9 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile50_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [26] (choices 3) [13,21,25,28] profile50_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile50_node10
  · exact profile50_node11
  · exact profile50_node16
  · exact profile50_node17

def profile50_node19_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 27 23 27 19), lower := (rows 29 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile50_node19 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28,25] 2 profile50_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28,25] 2 profile50_node19_cert).mp (by decide +kernel))

def profile50_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node18 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28] 2 (by decide) (choices 3) [25] profile50_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [28] (choices 3) [25] profile50_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node19

def profile50_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node0 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [] 2 (by decide) (choices 3) [14,22,26,28] profile50_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [] (choices 3) [14,22,26,28] profile50_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile50_node1
  · exact profile50_node3
  · exact profile50_node9
  · exact profile50_node18

theorem profile50 : Upper (D (n:=5) [51,51,49,34,19]) (R (n:=5) [51,51,49,34,19]) [] 2 := profile50_node0

def profile51_node3_cert : CutBound 5 := { lost := (rows 0 8 8 6 0), upper := (rows 15 23 23 25 25), lower := (rows 15 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile51_node3 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,19] 2 profile51_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,19] 2 profile51_node3_cert).mp (by decide +kernel))

def profile51_node5_cert : CutBound 5 := { lost := (rows 0 0 2 6 0), upper := (rows 15 23 29 25 18), lower := (rows 15 23 29 25 16), losses := [{ target := 1, region := (rows 1 0 14 14 16), good := (rows 13 29 29 29 16) },{ target := 2, region := (rows 1 2 0 15 19), good := (rows 27 27 25 25 16) }] }

theorem profile51_node5 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,17] 2 profile51_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,17] 2 profile51_node5_cert).mp (by decide +kernel))

def profile51_node6_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 15 23 29 26 17), lower := (rows 15 23 29 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 28 26 16) },{ target := 1, region := (rows 1 0 5 8 23), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 11 23), good := (rows 27 27 25 26 16) }] }

theorem profile51_node6 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,18] 2 profile51_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25,18] 2 profile51_node6_cert).mp (by decide +kernel))

def profile51_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node4 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25] 2 (by decide) (choices 2) [17,18] profile51_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,25] (choices 2) [17,18] profile51_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node5
  · exact profile51_node6

def profile51_node7_cert : CutBound 5 := { lost := (rows 0 8 0 6 0), upper := (rows 15 23 30 25 17), lower := (rows 15 23 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile51_node7 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,26] 2 profile51_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21,26] 2 profile51_node7_cert).mp (by decide +kernel))

def profile51_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node2 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21] 2 (by decide) (choices 3) [19,25,26] profile51_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,21] (choices 3) [19,25,26] profile51_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node3
  · exact profile51_node4
  · exact profile51_node7

def profile51_node10_cert : CutBound 5 := { lost := (rows 0 4 0 6 0), upper := (rows 15 27 23 25 20), lower := (rows 15 27 23 25 16), losses := [{ target := 1, region := (rows 1 0 4 15 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 14 0 14 16), good := (rows 11 27 27 27 16) }] }

theorem profile51_node10 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,17] 2 profile51_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,17] 2 profile51_node10_cert).mp (by decide +kernel))

def profile51_node11_cert : CutBound 5 := { lost := (rows 0 4 0 3 0), upper := (rows 15 27 23 28 17), lower := (rows 15 27 23 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 23), good := (rows 29 25 29 28 16) },{ target := 2, region := (rows 1 3 0 8 23), good := (rows 27 27 19 24 16) }] }

theorem profile51_node11 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,20] 2 profile51_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19,20] 2 profile51_node11_cert).mp (by decide +kernel))

def profile51_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node9 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19] 2 (by decide) (choices 2) [17,20] profile51_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25,19] (choices 2) [17,20] profile51_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node10
  · exact profile51_node11

def profile51_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node8 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25] 2 (by decide) (choices 3) [19] profile51_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,25] (choices 3) [19] profile51_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node9

def profile51_node12_cert : CutBound 5 := { lost := (rows 16 0 8 4 0), upper := (rows 15 30 23 27 19), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile51_node12 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,28] 2 profile51_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14,28] 2 profile51_node12_cert).mp (by decide +kernel))

def profile51_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node1 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14] 2 (by decide) (choices 3) [21,25,28] profile51_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [14] (choices 3) [21,25,28] profile51_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node2
  · exact profile51_node8
  · exact profile51_node12

def profile51_node15_cert : CutBound 5 := { lost := (rows 8 0 8 6 0), upper := (rows 23 15 23 25 25), lower := (rows 23 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile51_node15 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,19] 2 profile51_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,19] 2 profile51_node15_cert).mp (by decide +kernel))

def profile51_node16_cert : CutBound 5 := { lost := (rows 8 16 0 4 0), upper := (rows 23 15 29 27 19), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile51_node16 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,25] 2 profile51_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,25] 2 profile51_node16_cert).mp (by decide +kernel))

def profile51_node17_cert : CutBound 5 := { lost := (rows 8 0 0 6 0), upper := (rows 23 15 30 25 17), lower := (rows 23 15 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile51_node17 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,26] 2 profile51_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13,26] 2 profile51_node17_cert).mp (by decide +kernel))

def profile51_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node14 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13] 2 (by decide) (choices 3) [19,25,26] profile51_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,13] (choices 3) [19,25,26] profile51_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node15
  · exact profile51_node16
  · exact profile51_node17

def profile51_node18_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile51_node18 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,21] 2 profile51_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,21] 2 profile51_node18_cert).mp (by decide +kernel))

def profile51_node20_cert : CutBound 5 := { lost := (rows 8 0 16 2 0), upper := (rows 23 27 15 29 21), lower := (rows 23 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile51_node20 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,11] 2 profile51_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,11] 2 profile51_node20_cert).mp (by decide +kernel))

def profile51_node21_cert : CutBound 5 := { lost := (rows 8 0 8 2 0), upper := (rows 23 27 23 13 29), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile51_node21 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,19] 2 profile51_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,19] 2 profile51_node21_cert).mp (by decide +kernel))

def profile51_node22_cert : CutBound 5 := { lost := (rows 0 4 2 16 0), upper := (rows 23 27 29 15 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile51_node22 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,25] 2 profile51_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,25] 2 profile51_node22_cert).mp (by decide +kernel))

def profile51_node23_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 30 13 21), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile51_node23 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,26] 2 profile51_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25,26] 2 profile51_node23_cert).mp (by decide +kernel))

def profile51_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node19 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25] 2 (by decide) (choices 3) [11,19,25,26] profile51_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,25] (choices 3) [11,19,25,26] profile51_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile51_node20
  · exact profile51_node21
  · exact profile51_node22
  · exact profile51_node23

def profile51_node25_cert : CutBound 5 := { lost := (rows 8 0 0 6 0), upper := (rows 23 30 15 25 17), lower := (rows 23 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile51_node25 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,11] 2 profile51_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,11] 2 profile51_node25_cert).mp (by decide +kernel))

def profile51_node26_cert : CutBound 5 := { lost := (rows 8 0 8 6 0), upper := (rows 23 30 23 9 25), lower := (rows 23 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile51_node26 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,19] 2 profile51_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,19] 2 profile51_node26_cert).mp (by decide +kernel))

def profile51_node27_cert : CutBound 5 := { lost := (rows 8 1 0 4 0), upper := (rows 23 30 29 11 19), lower := (rows 23 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile51_node27 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,25] 2 profile51_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28,25] 2 profile51_node27_cert).mp (by decide +kernel))

def profile51_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node24 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28] 2 (by decide) (choices 3) [11,19,25] profile51_node24_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22,28] (choices 3) [11,19,25] profile51_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node25
  · exact profile51_node26
  · exact profile51_node27

def profile51_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node13 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22] 2 (by decide) (choices 3) [13,21,25,28] profile51_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [22] (choices 3) [13,21,25,28] profile51_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile51_node14
  · exact profile51_node18
  · exact profile51_node19
  · exact profile51_node24

def profile51_node31_cert : CutBound 5 := { lost := (rows 4 0 0 6 0), upper := (rows 27 15 23 25 20), lower := (rows 27 15 23 25 16), losses := [{ target := 1, region := (rows 1 0 4 15 22), good := (rows 25 29 29 25 16) },{ target := 2, region := (rows 5 2 0 13 16), good := (rows 27 11 27 25 16) }] }

theorem profile51_node31 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,17] 2 profile51_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,17] 2 profile51_node31_cert).mp (by decide +kernel))

def profile51_node32_cert : CutBound 5 := { lost := (rows 4 0 0 3 0), upper := (rows 27 15 23 28 17), lower := (rows 27 15 23 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 26 14 30 28 16) },{ target := 1, region := (rows 1 0 4 14 23), good := (rows 25 29 29 28 16) },{ target := 2, region := (rows 3 2 0 8 23), good := (rows 27 27 19 24 16) }] }

theorem profile51_node32 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,20] 2 profile51_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19,20] 2 profile51_node32_cert).mp (by decide +kernel))

def profile51_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node30 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19] 2 (by decide) (choices 2) [17,20] profile51_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13,19] (choices 2) [17,20] profile51_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node31
  · exact profile51_node32

def profile51_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node29 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13] 2 (by decide) (choices 3) [19] profile51_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,13] (choices 3) [19] profile51_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node30

def profile51_node34_cert : CutBound 5 := { lost := (rows 0 8 16 2 0), upper := (rows 27 23 15 29 21), lower := (rows 27 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile51_node34 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,11] 2 profile51_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,11] 2 profile51_node34_cert).mp (by decide +kernel))

def profile51_node35_cert : CutBound 5 := { lost := (rows 0 8 8 2 0), upper := (rows 27 23 23 13 29), lower := (rows 27 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile51_node35 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,19] 2 profile51_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,19] 2 profile51_node35_cert).mp (by decide +kernel))

def profile51_node36_cert : CutBound 5 := { lost := (rows 0 8 2 16 0), upper := (rows 27 23 29 15 23), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 13 8 0) }] }

theorem profile51_node36 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,25] 2 profile51_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,25] 2 profile51_node36_cert).mp (by decide +kernel))

def profile51_node37_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 23 30 13 21), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 19 27 8 16) }] }

theorem profile51_node37 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,26] 2 profile51_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21,26] 2 profile51_node37_cert).mp (by decide +kernel))

def profile51_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node33 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21] 2 (by decide) (choices 3) [11,19,25,26] profile51_node33_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,21] (choices 3) [11,19,25,26] profile51_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile51_node34
  · exact profile51_node35
  · exact profile51_node36
  · exact profile51_node37

def profile51_node38_cert : CutBound 5 := { lost := (rows 4 4 8 0 0), upper := (rows 27 27 23 31 23), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile51_node38 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,25] 2 profile51_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,25] 2 profile51_node38_cert).mp (by decide +kernel))

def profile51_node40_cert : CutBound 5 := { lost := (rows 4 0 8 2 0), upper := (rows 27 30 23 13 21), lower := (rows 27 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 19 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile51_node40 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28,19] 2 profile51_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28,19] 2 profile51_node40_cert).mp (by decide +kernel))

def profile51_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node39 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28] 2 (by decide) (choices 3) [19] profile51_node39_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26,28] (choices 3) [19] profile51_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node40

def profile51_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node28 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile51_node28_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [26] (choices 3) [13,21,25,28] profile51_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile51_node29
  · exact profile51_node33
  · exact profile51_node38
  · exact profile51_node39

def profile51_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile51_node0 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [] 2 (by decide) (choices 3) [14,22,26] profile51_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [] (choices 3) [14,22,26] profile51_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile51_node1
  · exact profile51_node13
  · exact profile51_node28

theorem profile51 : Upper (D (n:=5) [51,50,50,34,19]) (R (n:=5) [51,50,50,34,19]) [] 2 := profile51_node0

def profile52_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 29 29 29), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile52_node2 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,13] 2 profile52_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,13] 2 profile52_node2_cert).mp (by decide +kernel))

def profile52_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 29 29 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile52_node3 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,21] 2 profile52_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,21] 2 profile52_node3_cert).mp (by decide +kernel))

def profile52_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 29 29 29), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile52_node4 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,28] 2 profile52_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30,28] 2 profile52_node4_cert).mp (by decide +kernel))

def profile52_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile52_node1 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile52_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [30] (choices 3) [13,21,28] profile52_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile52_node2
  · exact profile52_node3
  · exact profile52_node4

def profile52_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node0 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [] 2 (by decide) (choices 4) [30] profile52_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [] (choices 4) [30] profile52_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node1

theorem profile52 : Upper (D (n:=5) [66,49,35,35,19]) (R (n:=5) [66,49,35,35,19]) [] 2 := profile52_node0

#print axioms profile52
end Delivery.FiveVertexPositive12
