import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile53_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile53_node2 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,13] 2 profile53_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,13] 2 profile53_node2_cert).mp (by decide +kernel))

def profile53_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 30 30 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile53_node3 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,21] 2 profile53_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,21] 2 profile53_node3_cert).mp (by decide +kernel))

def profile53_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 30 7 28 28), lower := (rows 31 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 28 29 8 16) }] }

theorem profile53_node5 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,3] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,3] 2 profile53_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,3] 2 profile53_node5_cert).mp (by decide +kernel))

def profile53_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 30 13 30 22), lower := (rows 31 30 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 13 8 16) }] }

theorem profile53_node6 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,9] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,9] 2 profile53_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,9] 2 profile53_node6_cert).mp (by decide +kernel))

def profile53_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 30 14 29 21), lower := (rows 31 30 14 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) }] }

theorem profile53_node7 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,10] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,10] 2 profile53_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,10] 2 profile53_node7_cert).mp (by decide +kernel))

def profile53_node8_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 30 21 14 30), lower := (rows 31 30 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 21 8 16) }] }

theorem profile53_node8 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,17] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,17] 2 profile53_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,17] 2 profile53_node8_cert).mp (by decide +kernel))

def profile53_node9_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 30 22 13 29), lower := (rows 31 30 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) }] }

theorem profile53_node9 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,18] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,18] 2 profile53_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,18] 2 profile53_node9_cert).mp (by decide +kernel))

def profile53_node10_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 30 28 15 23), lower := (rows 31 30 28 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 28 28 8 16) }] }

theorem profile53_node10 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,24] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,24] 2 profile53_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28,24] 2 profile53_node10_cert).mp (by decide +kernel))

def profile53_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node4 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile53_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30,28] (choices 2) [3,9,10,17,18,24] profile53_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile53_node5
  · exact profile53_node6
  · exact profile53_node7
  · exact profile53_node8
  · exact profile53_node9
  · exact profile53_node10

def profile53_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile53_node1 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile53_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [30] (choices 3) [13,21,28] profile53_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile53_node2
  · exact profile53_node3
  · exact profile53_node4

def profile53_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node0 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [] 2 (by decide) (choices 4) [30] profile53_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [] (choices 4) [30] profile53_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node1

theorem profile53 : Upper (D (n:=5) [65,50,35,35,19]) (R (n:=5) [65,50,35,35,19]) [] 2 := profile53_node0

def profile54_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 27 23 25 25), lower := (rows 15 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile54_node3 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,19] 2 profile54_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,19] 2 profile54_node3_cert).mp (by decide +kernel))

def profile54_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 27 29 27 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) }] }

theorem profile54_node4 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,25] 2 profile54_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,25] 2 profile54_node4_cert).mp (by decide +kernel))

def profile54_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 27 30 25 17), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) }] }

theorem profile54_node5 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,26] 2 profile54_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25,26] 2 profile54_node5_cert).mp (by decide +kernel))

def profile54_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node2 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25] 2 (by decide) (choices 3) [19,25,26] profile54_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14,25] (choices 3) [19,25,26] profile54_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node3
  · exact profile54_node4
  · exact profile54_node5

def profile54_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node1 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14] 2 (by decide) (choices 3) [25] profile54_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [14] (choices 3) [25] profile54_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node2

def profile54_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 15 25 25), lower := (rows 23 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile54_node8 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,11] 2 profile54_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,11] 2 profile54_node8_cert).mp (by decide +kernel))

def profile54_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 27 29 11 27), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) }] }

theorem profile54_node9 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,25] 2 profile54_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,25] 2 profile54_node9_cert).mp (by decide +kernel))

def profile54_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 30 9 25), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) }] }

theorem profile54_node10 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,26] 2 profile54_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25,26] 2 profile54_node10_cert).mp (by decide +kernel))

def profile54_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node7 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25] 2 (by decide) (choices 3) [11,25,26] profile54_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22,25] (choices 3) [11,25,26] profile54_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node8
  · exact profile54_node9
  · exact profile54_node10

def profile54_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node6 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22] 2 (by decide) (choices 3) [25] profile54_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [22] (choices 3) [25] profile54_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node7

def profile54_node13_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 15 23 25 25), lower := (rows 27 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile54_node13 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,19] 2 profile54_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,19] 2 profile54_node13_cert).mp (by decide +kernel))

def profile54_node14_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 15 29 27 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) }] }

theorem profile54_node14 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,25] 2 profile54_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,25] 2 profile54_node14_cert).mp (by decide +kernel))

def profile54_node15_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 15 30 25 17), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) }] }

theorem profile54_node15 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,26] 2 profile54_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13,26] 2 profile54_node15_cert).mp (by decide +kernel))

def profile54_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node12 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13] 2 (by decide) (choices 3) [19,25,26] profile54_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,13] (choices 3) [19,25,26] profile54_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node13
  · exact profile54_node14
  · exact profile54_node15

def profile54_node17_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 15 25 25), lower := (rows 27 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile54_node17 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,11] 2 profile54_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,11] 2 profile54_node17_cert).mp (by decide +kernel))

def profile54_node18_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 23 29 11 27), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile54_node18 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,25] 2 profile54_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,25] 2 profile54_node18_cert).mp (by decide +kernel))

def profile54_node19_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 30 9 25), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) }] }

theorem profile54_node19 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,26] 2 profile54_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21,26] 2 profile54_node19_cert).mp (by decide +kernel))

def profile54_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node16 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21] 2 (by decide) (choices 3) [11,25,26] profile54_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,21] (choices 3) [11,25,26] profile54_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node17
  · exact profile54_node18
  · exact profile54_node19

def profile54_node21_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 27 15 29 21), lower := (rows 27 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) }] }

theorem profile54_node21 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,11] 2 profile54_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,11] 2 profile54_node21_cert).mp (by decide +kernel))

def profile54_node22_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 27 23 13 29), lower := (rows 27 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) }] }

theorem profile54_node22 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,19] 2 profile54_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,19] 2 profile54_node22_cert).mp (by decide +kernel))

def profile54_node23_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 27 29 15 23), lower := (rows 27 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile54_node23 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,25] 2 profile54_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,25] 2 profile54_node23_cert).mp (by decide +kernel))

def profile54_node24_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 27 30 13 21), lower := (rows 27 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile54_node24 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,26] 2 profile54_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25,26] 2 profile54_node24_cert).mp (by decide +kernel))

def profile54_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node20 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25] 2 (by decide) (choices 3) [11,19,25,26] profile54_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,25] (choices 3) [11,19,25,26] profile54_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile54_node21
  · exact profile54_node22
  · exact profile54_node23
  · exact profile54_node24

def profile54_node26_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 30 15 25 17), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile54_node26 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,11] 2 profile54_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,11] 2 profile54_node26_cert).mp (by decide +kernel))

def profile54_node27_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 30 23 9 25), lower := (rows 27 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile54_node27 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,19] 2 profile54_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,19] 2 profile54_node27_cert).mp (by decide +kernel))

def profile54_node28_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 27 30 29 11 19), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) }] }

theorem profile54_node28 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,25] 2 profile54_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28,25] 2 profile54_node28_cert).mp (by decide +kernel))

def profile54_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node25 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28] 2 (by decide) (choices 3) [11,19,25] profile54_node25_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26,28] (choices 3) [11,19,25] profile54_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile54_node26
  · exact profile54_node27
  · exact profile54_node28

def profile54_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node11 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile54_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [26] (choices 3) [13,21,25,28] profile54_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile54_node12
  · exact profile54_node16
  · exact profile54_node20
  · exact profile54_node25

def profile54_node31_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 29 27 15 27 19), lower := (rows 29 27 15 8 16), losses := [{ target := 4, region := (rows 1 2 6 8 0), good := (rows 13 15 15 8 0) }] }

theorem profile54_node31 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,11] 2 profile54_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,11] 2 profile54_node31_cert).mp (by decide +kernel))

def profile54_node32_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 27 23 11 27), lower := (rows 29 27 23 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 23 23 0 16) }] }

theorem profile54_node32 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,19] 2 profile54_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,19] 2 profile54_node32_cert).mp (by decide +kernel))

def profile54_node33_cert : CutBound 5 := { lost := (rows 2 0 2 0 0), upper := (rows 29 27 29 11 19), lower := (rows 29 27 29 8 16), losses := [{ target := 1, region := (rows 7 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile54_node33 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,25] 2 profile54_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,25] 2 profile54_node33_cert).mp (by decide +kernel))

def profile54_node34_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 29 27 30 11 19), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) }] }

theorem profile54_node34 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,26] 2 profile54_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25,26] 2 profile54_node34_cert).mp (by decide +kernel))

def profile54_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node30 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25] 2 (by decide) (choices 3) [11,19,25,26] profile54_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28,25] (choices 3) [11,19,25,26] profile54_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile54_node31
  · exact profile54_node32
  · exact profile54_node33
  · exact profile54_node34

def profile54_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node29 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28] 2 (by decide) (choices 3) [25] profile54_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [28] (choices 3) [25] profile54_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node30

def profile54_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node0 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [] 2 (by decide) (choices 3) [14,22,26,28] profile54_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [] (choices 3) [14,22,26,28] profile54_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile54_node1
  · exact profile54_node6
  · exact profile54_node11
  · exact profile54_node29

theorem profile54 : Upper (D (n:=5) [51,50,49,35,19]) (R (n:=5) [51,50,49,35,19]) [] 2 := profile54_node0

def profile55_node3_cert : CutBound 5 := { lost := (rows 0 8 0 5 0), upper := (rows 15 23 29 26 26), lower := (rows 15 23 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile55_node3 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,25] 2 profile55_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,25] 2 profile55_node3_cert).mp (by decide +kernel))

def profile55_node4_cert : CutBound 5 := { lost := (rows 16 0 0 6 0), upper := (rows 15 23 30 25 25), lower := (rows 15 23 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile55_node4 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,26] 2 profile55_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21,26] 2 profile55_node4_cert).mp (by decide +kernel))

def profile55_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node2 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21] 2 (by decide) (choices 3) [25,26] profile55_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,21] (choices 3) [25,26] profile55_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile55_node3
  · exact profile55_node4

def profile55_node6_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 15 27 23 28 28), lower := (rows 15 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile55_node6 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,19] 2 profile55_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,19] 2 profile55_node6_cert).mp (by decide +kernel))

def profile55_node7_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 15 27 29 30 22), lower := (rows 15 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 27 27 8 16) }] }

theorem profile55_node7 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,25] 2 profile55_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,25] 2 profile55_node7_cert).mp (by decide +kernel))

def profile55_node8_cert : CutBound 5 := { lost := (rows 16 0 1 2 0), upper := (rows 15 27 30 29 21), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 15 11 15 8 0) }] }

theorem profile55_node8 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,26] 2 profile55_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25,26] 2 profile55_node8_cert).mp (by decide +kernel))

def profile55_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node5 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25] 2 (by decide) (choices 3) [19,25,26] profile55_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,25] (choices 3) [19,25,26] profile55_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node6
  · exact profile55_node7
  · exact profile55_node8

def profile55_node10_cert : CutBound 5 := { lost := (rows 16 0 0 6 0), upper := (rows 15 30 23 25 25), lower := (rows 15 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile55_node10 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,19] 2 profile55_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,19] 2 profile55_node10_cert).mp (by decide +kernel))

def profile55_node11_cert : CutBound 5 := { lost := (rows 16 1 0 4 0), upper := (rows 15 30 29 27 19), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 13 8 0) }] }

theorem profile55_node11 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,25] 2 profile55_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,25] 2 profile55_node11_cert).mp (by decide +kernel))

def profile55_node12_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 15 30 30 25 17), lower := (rows 15 30 30 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) }] }

theorem profile55_node12 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,26] 2 profile55_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28,26] 2 profile55_node12_cert).mp (by decide +kernel))

def profile55_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node9 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28] 2 (by decide) (choices 3) [19,25,26] profile55_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14,28] (choices 3) [19,25,26] profile55_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node10
  · exact profile55_node11
  · exact profile55_node12

def profile55_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node1 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14] 2 (by decide) (choices 3) [21,25,28] profile55_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [14] (choices 3) [21,25,28] profile55_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node2
  · exact profile55_node5
  · exact profile55_node9

def profile55_node15_cert : CutBound 5 := { lost := (rows 0 16 0 5 0), upper := (rows 23 15 29 26 26), lower := (rows 23 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile55_node15 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,25] 2 profile55_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,25] 2 profile55_node15_cert).mp (by decide +kernel))

def profile55_node16_cert : CutBound 5 := { lost := (rows 8 0 0 6 0), upper := (rows 23 15 30 25 25), lower := (rows 23 15 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile55_node16 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,26] 2 profile55_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13,26] 2 profile55_node16_cert).mp (by decide +kernel))

def profile55_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node14 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13] 2 (by decide) (choices 3) [25,26] profile55_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,13] (choices 3) [25,26] profile55_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile55_node15
  · exact profile55_node16

def profile55_node18_cert : CutBound 5 := { lost := (rows 0 0 16 3 0), upper := (rows 23 27 15 28 28), lower := (rows 23 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile55_node18 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,11] 2 profile55_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,11] 2 profile55_node18_cert).mp (by decide +kernel))

def profile55_node19_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 23 27 29 14 30), lower := (rows 23 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) }] }

theorem profile55_node19 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,25] 2 profile55_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,25] 2 profile55_node19_cert).mp (by decide +kernel))

def profile55_node20_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 30 13 29), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 23 19 23 0 16) }] }

theorem profile55_node20 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,26] 2 profile55_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25,26] 2 profile55_node20_cert).mp (by decide +kernel))

def profile55_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node17 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25] 2 (by decide) (choices 3) [11,25,26] profile55_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,25] (choices 3) [11,25,26] profile55_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node18
  · exact profile55_node19
  · exact profile55_node20

def profile55_node22_cert : CutBound 5 := { lost := (rows 8 0 0 6 0), upper := (rows 23 30 15 25 25), lower := (rows 23 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile55_node22 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,11] 2 profile55_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,11] 2 profile55_node22_cert).mp (by decide +kernel))

def profile55_node23_cert : CutBound 5 := { lost := (rows 8 1 0 4 0), upper := (rows 23 30 29 11 27), lower := (rows 23 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 21 0 16) }] }

theorem profile55_node23 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,25] 2 profile55_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,25] 2 profile55_node23_cert).mp (by decide +kernel))

def profile55_node24_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 23 30 30 9 25), lower := (rows 23 30 30 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) }] }

theorem profile55_node24 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,26] 2 profile55_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28,26] 2 profile55_node24_cert).mp (by decide +kernel))

def profile55_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node21 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28] 2 (by decide) (choices 3) [11,25,26] profile55_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22,28] (choices 3) [11,25,26] profile55_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node22
  · exact profile55_node23
  · exact profile55_node24

def profile55_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node13 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22] 2 (by decide) (choices 3) [13,25,28] profile55_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [22] (choices 3) [13,25,28] profile55_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node14
  · exact profile55_node17
  · exact profile55_node21

def profile55_node27_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 27 15 23 28 28), lower := (rows 27 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile55_node27 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,19] 2 profile55_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,19] 2 profile55_node27_cert).mp (by decide +kernel))

def profile55_node28_cert : CutBound 5 := { lost := (rows 0 16 2 1 0), upper := (rows 27 15 29 30 22), lower := (rows 27 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 8 0), good := (rows 11 15 15 8 0) }] }

theorem profile55_node28 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,25] 2 profile55_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,25] 2 profile55_node28_cert).mp (by decide +kernel))

def profile55_node29_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 15 30 29 21), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 11 27 8 16) }] }

theorem profile55_node29 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,26] 2 profile55_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13,26] 2 profile55_node29_cert).mp (by decide +kernel))

def profile55_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node26 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13] 2 (by decide) (choices 3) [19,25,26] profile55_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,13] (choices 3) [19,25,26] profile55_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node27
  · exact profile55_node28
  · exact profile55_node29

def profile55_node31_cert : CutBound 5 := { lost := (rows 0 0 16 3 0), upper := (rows 27 23 15 28 28), lower := (rows 27 23 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile55_node31 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,11] 2 profile55_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,11] 2 profile55_node31_cert).mp (by decide +kernel))

def profile55_node32_cert : CutBound 5 := { lost := (rows 0 8 2 1 0), upper := (rows 27 23 29 14 30), lower := (rows 27 23 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 19 23 23 0 16) }] }

theorem profile55_node32 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,25] 2 profile55_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,25] 2 profile55_node32_cert).mp (by decide +kernel))

def profile55_node33_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 23 30 13 29), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 19 27 8 16) }] }

theorem profile55_node33 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,26] 2 profile55_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21,26] 2 profile55_node33_cert).mp (by decide +kernel))

def profile55_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node30 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21] 2 (by decide) (choices 3) [11,25,26] profile55_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,21] (choices 3) [11,25,26] profile55_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node31
  · exact profile55_node32
  · exact profile55_node33

def profile55_node35_cert : CutBound 5 := { lost := (rows 4 4 0 3 0), upper := (rows 27 27 15 28 20), lower := (rows 27 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 26 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 11 8 16) }] }

theorem profile55_node35 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,11] 2 profile55_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,11] 2 profile55_node35_cert).mp (by decide +kernel))

def profile55_node36_cert : CutBound 5 := { lost := (rows 4 4 0 3 0), upper := (rows 27 27 23 12 28), lower := (rows 27 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 26 30 8 16) },{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 25 29 8 16) },{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 19 8 16) }] }

theorem profile55_node36 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,19] 2 profile55_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,19] 2 profile55_node36_cert).mp (by decide +kernel))

def profile55_node37_cert : CutBound 5 := { lost := (rows 4 4 2 0 0), upper := (rows 27 27 29 14 22), lower := (rows 27 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile55_node37 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,25] 2 profile55_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,25] 2 profile55_node37_cert).mp (by decide +kernel))

def profile55_node38_cert : CutBound 5 := { lost := (rows 4 4 1 0 0), upper := (rows 27 27 30 13 21), lower := (rows 27 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 7 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile55_node38 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,26] 2 profile55_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25,26] 2 profile55_node38_cert).mp (by decide +kernel))

def profile55_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node34 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25] 2 (by decide) (choices 3) [11,19,25,26] profile55_node34_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,25] (choices 3) [11,19,25,26] profile55_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile55_node35
  · exact profile55_node36
  · exact profile55_node37
  · exact profile55_node38

def profile55_node40_cert : CutBound 5 := { lost := (rows 4 0 16 2 0), upper := (rows 27 30 15 29 21), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile55_node40 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,11] 2 profile55_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,11] 2 profile55_node40_cert).mp (by decide +kernel))

def profile55_node41_cert : CutBound 5 := { lost := (rows 4 0 8 2 0), upper := (rows 27 30 23 13 29), lower := (rows 27 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 19 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 22 23 0 16) }] }

theorem profile55_node41 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,19] 2 profile55_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,19] 2 profile55_node41_cert).mp (by decide +kernel))

def profile55_node42_cert : CutBound 5 := { lost := (rows 4 1 2 0 0), upper := (rows 27 30 29 15 23), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 25 8 16) }] }

theorem profile55_node42 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,25] 2 profile55_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,25] 2 profile55_node42_cert).mp (by decide +kernel))

def profile55_node43_cert : CutBound 5 := { lost := (rows 4 1 1 0 0), upper := (rows 27 30 30 13 21), lower := (rows 27 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 7 2 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile55_node43 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,26] 2 profile55_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28,26] 2 profile55_node43_cert).mp (by decide +kernel))

def profile55_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node39 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28] 2 (by decide) (choices 3) [11,19,25,26] profile55_node39_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26,28] (choices 3) [11,19,25,26] profile55_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile55_node40
  · exact profile55_node41
  · exact profile55_node42
  · exact profile55_node43

def profile55_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node25 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile55_node25_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [26] (choices 3) [13,21,25,28] profile55_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile55_node26
  · exact profile55_node30
  · exact profile55_node34
  · exact profile55_node39

def profile55_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile55_node0 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [] 2 (by decide) (choices 3) [14,22,26] profile55_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [] (choices 3) [14,22,26] profile55_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile55_node1
  · exact profile55_node13
  · exact profile55_node25

theorem profile55 : Upper (D (n:=5) [50,50,50,35,19]) (R (n:=5) [50,50,50,35,19]) [] 2 := profile55_node0

def profile56_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 27 29 26 26), lower := (rows 15 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 26 28 8 16) }] }

theorem profile56_node3 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,25] 2 profile56_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,25] 2 profile56_node3_cert).mp (by decide +kernel))

def profile56_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 27 30 25 25), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) }] }

theorem profile56_node4 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,26] 2 profile56_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25,26] 2 profile56_node4_cert).mp (by decide +kernel))

def profile56_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node2 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25] 2 (by decide) (choices 3) [25,26] profile56_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14,25] (choices 3) [25,26] profile56_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile56_node3
  · exact profile56_node4

def profile56_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node1 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14] 2 (by decide) (choices 3) [25] profile56_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [14] (choices 3) [25] profile56_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node2

def profile56_node7_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 15 29 26 26), lower := (rows 27 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 26 30 28 8 16) }] }

theorem profile56_node7 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,25] 2 profile56_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,25] 2 profile56_node7_cert).mp (by decide +kernel))

def profile56_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 15 30 25 25), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) }] }

theorem profile56_node8 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,26] 2 profile56_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13,26] 2 profile56_node8_cert).mp (by decide +kernel))

def profile56_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node6 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13] 2 (by decide) (choices 3) [25,26] profile56_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,13] (choices 3) [25,26] profile56_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile56_node7
  · exact profile56_node8

def profile56_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 27 15 28 28), lower := (rows 27 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 26 30 8 16) }] }

theorem profile56_node10 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,11] 2 profile56_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,11] 2 profile56_node10_cert).mp (by decide +kernel))

def profile56_node11_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 27 29 14 30), lower := (rows 27 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile56_node11 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,25] 2 profile56_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,25] 2 profile56_node11_cert).mp (by decide +kernel))

def profile56_node12_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 27 30 13 29), lower := (rows 27 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile56_node12 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,26] 2 profile56_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25,26] 2 profile56_node12_cert).mp (by decide +kernel))

def profile56_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node9 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25] 2 (by decide) (choices 3) [11,25,26] profile56_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,25] (choices 3) [11,25,26] profile56_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile56_node10
  · exact profile56_node11
  · exact profile56_node12

def profile56_node14_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 30 15 25 25), lower := (rows 27 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile56_node14 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,11] 2 profile56_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,11] 2 profile56_node14_cert).mp (by decide +kernel))

def profile56_node15_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 27 30 29 11 27), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) }] }

theorem profile56_node15 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,25] 2 profile56_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,25] 2 profile56_node15_cert).mp (by decide +kernel))

def profile56_node16_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 27 30 30 9 25), lower := (rows 27 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile56_node16 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,26] 2 profile56_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28,26] 2 profile56_node16_cert).mp (by decide +kernel))

def profile56_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node13 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28] 2 (by decide) (choices 3) [11,25,26] profile56_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26,28] (choices 3) [11,25,26] profile56_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile56_node14
  · exact profile56_node15
  · exact profile56_node16

def profile56_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node5 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26] 2 (by decide) (choices 3) [13,25,28] profile56_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [26] (choices 3) [13,25,28] profile56_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile56_node6
  · exact profile56_node9
  · exact profile56_node13

def profile56_node19_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 27 15 26 26), lower := (rows 29 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 26 30 8 16) }] }

theorem profile56_node19 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,11] 2 profile56_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,11] 2 profile56_node19_cert).mp (by decide +kernel))

def profile56_node20_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 27 29 10 26), lower := (rows 29 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 26 28 8 16) }] }

theorem profile56_node20 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,25] 2 profile56_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,25] 2 profile56_node20_cert).mp (by decide +kernel))

def profile56_node21_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 29 27 30 11 27), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) }] }

theorem profile56_node21 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,26] 2 profile56_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25,26] 2 profile56_node21_cert).mp (by decide +kernel))

def profile56_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node18 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25] 2 (by decide) (choices 3) [11,25,26] profile56_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28,25] (choices 3) [11,25,26] profile56_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile56_node19
  · exact profile56_node20
  · exact profile56_node21

def profile56_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node17 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28] 2 (by decide) (choices 3) [25] profile56_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [28] (choices 3) [25] profile56_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node18

def profile56_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node0 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [] 2 (by decide) (choices 3) [14,26,28] profile56_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [] (choices 3) [14,26,28] profile56_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile56_node1
  · exact profile56_node5
  · exact profile56_node17

theorem profile56 : Upper (D (n:=5) [50,50,49,36,19]) (R (n:=5) [50,50,49,36,19]) [] 2 := profile56_node0

def profile57_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 23 27 19), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile57_node2 : Upper (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30,21] 2 profile57_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30,21] 2 profile57_node2_cert).mp (by decide +kernel))

def profile57_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node1 : Upper (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30] 2 (by decide) (choices 3) [21] profile57_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [30] (choices 3) [21] profile57_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node2

def profile57_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node0 : Upper (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [] 2 (by decide) (choices 4) [30] profile57_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [] (choices 4) [30] profile57_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node1

theorem profile57 : Upper (D (n:=5) [67,50,34,33,20]) (R (n:=5) [67,50,34,33,20]) [] 2 := profile57_node0

def profile58_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 23 27 19), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile58_node2 : Upper (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30,21] 2 profile58_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30,21] 2 profile58_node2_cert).mp (by decide +kernel))

def profile58_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node1 : Upper (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30] 2 (by decide) (choices 3) [21] profile58_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [30] (choices 3) [21] profile58_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node2

def profile58_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node0 : Upper (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [] 2 (by decide) (choices 4) [30] profile58_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [] (choices 4) [30] profile58_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node1

theorem profile58 : Upper (D (n:=5) [66,51,34,33,20]) (R (n:=5) [66,51,34,33,20]) [] 2 := profile58_node0

def profile59_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 23 21 30 22), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile59_node3 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,17] 2 profile59_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,17] 2 profile59_node3_cert).mp (by decide +kernel))

def profile59_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 23 22 29 21), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile59_node4 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,18] 2 profile59_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21,18] 2 profile59_node4_cert).mp (by decide +kernel))

def profile59_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node2 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21] 2 (by decide) (choices 2) [17,18] profile59_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30,21] (choices 2) [17,18] profile59_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile59_node3
  · exact profile59_node4

def profile59_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node1 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30] 2 (by decide) (choices 3) [21] profile59_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [30] (choices 3) [21] profile59_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node2

def profile59_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node0 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [] 2 (by decide) (choices 4) [30] profile59_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [] (choices 4) [30] profile59_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node1

theorem profile59 : Upper (D (n:=5) [66,50,35,33,20]) (R (n:=5) [66,50,35,33,20]) [] 2 := profile59_node0

def profile60_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile60_node2 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,21] 2 profile60_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,21] 2 profile60_node2_cert).mp (by decide +kernel))

def profile60_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 23 29 21), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile60_node4 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25,19] 2 profile60_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25,19] 2 profile60_node4_cert).mp (by decide +kernel))

def profile60_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node3 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25] 2 (by decide) (choices 3) [19] profile60_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,25] (choices 3) [19] profile60_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node4

def profile60_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 23 27 19), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile60_node5 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,28] 2 profile60_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22,28] 2 profile60_node5_cert).mp (by decide +kernel))

def profile60_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node1 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22] 2 (by decide) (choices 3) [21,25,28] profile60_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [22] (choices 3) [21,25,28] profile60_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile60_node2
  · exact profile60_node3
  · exact profile60_node5

def profile60_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 23 29 21), lower := (rows 27 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile60_node8 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21,19] 2 profile60_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21,19] 2 profile60_node8_cert).mp (by decide +kernel))

def profile60_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node7 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21] 2 (by decide) (choices 3) [19] profile60_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26,21] (choices 3) [19] profile60_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node8

def profile60_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node6 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26] 2 (by decide) (choices 3) [21] profile60_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [26] (choices 3) [21] profile60_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node7

def profile60_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile60_node0 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [] 2 (by decide) (choices 3) [22,26] profile60_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [] (choices 3) [22,26] profile60_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile60_node1
  · exact profile60_node6

theorem profile60 : Upper (D (n:=5) [51,50,50,33,20]) (R (n:=5) [51,50,50,33,20]) [] 2 := profile60_node0

def profile61_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 29 25 25), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile61_node2 : Upper (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,21] 2 profile61_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,21] 2 profile61_node2_cert).mp (by decide +kernel))

def profile61_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 21 25 17), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile61_node3 : Upper (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,28] 2 profile61_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30,28] 2 profile61_node3_cert).mp (by decide +kernel))

def profile61_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile61_node1 : Upper (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30] 2 (by decide) (choices 3) [21,28] profile61_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [30] (choices 3) [21,28] profile61_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile61_node2
  · exact profile61_node3

def profile61_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node0 : Upper (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [] 2 (by decide) (choices 4) [30] profile61_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [] (choices 4) [30] profile61_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node1

theorem profile61 : Upper (D (n:=5) [67,49,34,34,20]) (R (n:=5) [67,49,34,34,20]) [] 2 := profile61_node0

def profile62_node3_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 31 23 21 26 26), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile62_node3 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,17] 2 profile62_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,17] 2 profile62_node3_cert).mp (by decide +kernel))

def profile62_node4_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 31 23 22 25 25), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile62_node4 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,18] 2 profile62_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,18] 2 profile62_node4_cert).mp (by decide +kernel))

def profile62_node5_cert : CutBound 5 := { lost := (rows 0 0 3 4 0), upper := (rows 31 23 28 27 19), lower := (rows 31 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) }] }

theorem profile62_node5 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,24] 2 :=
  cut_bound_sound (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,24] 2 profile62_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21,24] 2 profile62_node5_cert).mp (by decide +kernel))

def profile62_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node2 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21] 2 (by decide) (choices 2) [17,18,24] profile62_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,21] (choices 2) [17,18,24] profile62_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile62_node3
  · exact profile62_node4
  · exact profile62_node5

def profile62_node6_cert : CutBound 5 := { lost := (rows 0 1 8 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile62_node6 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,28] 2 profile62_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30,28] 2 profile62_node6_cert).mp (by decide +kernel))

def profile62_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile62_node1 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30] 2 (by decide) (choices 3) [21,28] profile62_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [30] (choices 3) [21,28] profile62_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile62_node2
  · exact profile62_node6

def profile62_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node0 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [] 2 (by decide) (choices 4) [30] profile62_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [] (choices 4) [30] profile62_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node1

theorem profile62 : Upper (D (n:=5) [66,50,34,34,20]) (R (n:=5) [66,50,34,34,20]) [] 2 := profile62_node0

def profile63_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 30 26 26), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile63_node2 : Upper (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,21] 2 profile63_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,21] 2 profile63_node2_cert).mp (by decide +kernel))

def profile63_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile63_node3 : Upper (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,28] 2 profile63_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30,28] 2 profile63_node3_cert).mp (by decide +kernel))

def profile63_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile63_node1 : Upper (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30] 2 (by decide) (choices 3) [21,28] profile63_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [30] (choices 3) [21,28] profile63_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile63_node2
  · exact profile63_node3

def profile63_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node0 : Upper (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [] 2 (by decide) (choices 4) [30] profile63_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [] (choices 4) [30] profile63_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile63_node1

theorem profile63 : Upper (D (n:=5) [65,51,34,34,20]) (R (n:=5) [65,51,34,34,20]) [] 2 := profile63_node0

def profile64_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 29 29 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile64_node2 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,21] 2 profile64_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,21] 2 profile64_node2_cert).mp (by decide +kernel))

def profile64_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 21 29 21), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile64_node3 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,25] 2 profile64_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,25] 2 profile64_node3_cert).mp (by decide +kernel))

def profile64_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 21 29 21), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile64_node4 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,28] 2 profile64_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30,28] 2 profile64_node4_cert).mp (by decide +kernel))

def profile64_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile64_node1 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile64_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [30] (choices 3) [21,25,28] profile64_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile64_node2
  · exact profile64_node3
  · exact profile64_node4

def profile64_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile64_node0 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [] 2 (by decide) (choices 4) [30] profile64_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [] (choices 4) [30] profile64_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile64_node1

theorem profile64 : Upper (D (n:=5) [66,49,35,34,20]) (R (n:=5) [66,49,35,34,20]) [] 2 := profile64_node0

def profile65_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 30 30 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile65_node2 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,21] 2 profile65_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,21] 2 profile65_node2_cert).mp (by decide +kernel))

def profile65_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 22 30 22), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile65_node3 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,25] 2 profile65_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,25] 2 profile65_node3_cert).mp (by decide +kernel))

def profile65_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile65_node4 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,28] 2 profile65_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30,28] 2 profile65_node4_cert).mp (by decide +kernel))

def profile65_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile65_node1 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile65_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [30] (choices 3) [21,25,28] profile65_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile65_node2
  · exact profile65_node3
  · exact profile65_node4

def profile65_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile65_node0 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [] 2 (by decide) (choices 4) [30] profile65_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [] (choices 4) [30] profile65_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile65_node1

theorem profile65 : Upper (D (n:=5) [65,50,35,34,20]) (R (n:=5) [65,50,35,34,20]) [] 2 := profile65_node0

def profile66_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 23 25 25), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile66_node3 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,19] 2 profile66_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,19] 2 profile66_node3_cert).mp (by decide +kernel))

def profile66_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 27 29 27 19), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) }] }

theorem profile66_node4 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,25] 2 profile66_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,25] 2 profile66_node4_cert).mp (by decide +kernel))

def profile66_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 30 25 17), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) }] }

theorem profile66_node5 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,26] 2 profile66_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25,26] 2 profile66_node5_cert).mp (by decide +kernel))

def profile66_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node2 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25] 2 (by decide) (choices 3) [19,25,26] profile66_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22,25] (choices 3) [19,25,26] profile66_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node3
  · exact profile66_node4
  · exact profile66_node5

def profile66_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node1 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22] 2 (by decide) (choices 3) [25] profile66_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [22] (choices 3) [25] profile66_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node2

def profile66_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 23 25 25), lower := (rows 27 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile66_node8 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,19] 2 profile66_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,19] 2 profile66_node8_cert).mp (by decide +kernel))

def profile66_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 23 29 27 19), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile66_node9 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,25] 2 profile66_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,25] 2 profile66_node9_cert).mp (by decide +kernel))

def profile66_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 30 25 17), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) }] }

theorem profile66_node10 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,26] 2 profile66_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21,26] 2 profile66_node10_cert).mp (by decide +kernel))

def profile66_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node7 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21] 2 (by decide) (choices 3) [19,25,26] profile66_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,21] (choices 3) [19,25,26] profile66_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node8
  · exact profile66_node9
  · exact profile66_node10

def profile66_node11_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 27 23 31 23), lower := (rows 27 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile66_node11 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,25] 2 profile66_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,25] 2 profile66_node11_cert).mp (by decide +kernel))

def profile66_node12_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 30 23 27 19), lower := (rows 27 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile66_node12 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,28] 2 profile66_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26,28] 2 profile66_node12_cert).mp (by decide +kernel))

def profile66_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node6 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26] 2 (by decide) (choices 3) [21,25,28] profile66_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [26] (choices 3) [21,25,28] profile66_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node7
  · exact profile66_node11
  · exact profile66_node12

def profile66_node14_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 27 23 27 19), lower := (rows 29 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile66_node14 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28,25] 2 profile66_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28,25] 2 profile66_node14_cert).mp (by decide +kernel))

def profile66_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node13 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28] 2 (by decide) (choices 3) [25] profile66_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [28] (choices 3) [25] profile66_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node14

def profile66_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node0 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [] 2 (by decide) (choices 3) [22,26,28] profile66_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [] (choices 3) [22,26,28] profile66_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile66_node1
  · exact profile66_node6
  · exact profile66_node13

theorem profile66 : Upper (D (n:=5) [51,50,49,34,20]) (R (n:=5) [51,50,49,34,20]) [] 2 := profile66_node0

#print axioms profile66
end Delivery.FiveVertexPositive12
