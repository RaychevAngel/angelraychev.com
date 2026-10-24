import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile24_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 29 25 25), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile24_node2 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,21] 3 profile24_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,21] 3 profile24_node2_cert).mp (by decide +kernel))

def profile24_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 30 21 25 17), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile24_node3 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,28] 3 profile24_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14,28] 3 profile24_node3_cert).mp (by decide +kernel))

def profile24_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile24_node1 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14] 3 (by decide) (choices 3) [21,28] profile24_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [14] (choices 3) [21,28] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile24_node2
  · exact profile24_node3

def profile24_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 29 25 25), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile24_node5 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,13] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,13] 3 profile24_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,13] 3 profile24_node5_cert).mp (by decide +kernel))

def profile24_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 29 25 25), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile24_node6 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,21] 3 profile24_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,21] 3 profile24_node6_cert).mp (by decide +kernel))

def profile24_node8_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 23 27 13 29 21), lower := (rows 23 27 13 8 16), losses := [{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 13 8 0) }] }

theorem profile24_node8 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,9] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,9] 3 profile24_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,9] 3 profile24_node8_cert).mp (by decide +kernel))

def profile24_node9_cert : CutBound 5 := { lost := (rows 8 0 8 0 0), upper := (rows 23 27 21 13 29), lower := (rows 23 27 21 8 16), losses := [{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 21 0 16) }] }

theorem profile24_node9 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,17] 3 profile24_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,17] 3 profile24_node9_cert).mp (by decide +kernel))

def profile24_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 28 13 21), lower := (rows 23 27 28 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 28 8 16) }] }

theorem profile24_node10 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,24] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,24] 3 profile24_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25,24] 3 profile24_node10_cert).mp (by decide +kernel))

def profile24_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node7 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25] 3 (by decide) (choices 2) [9,17,24] profile24_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,25] (choices 2) [9,17,24] profile24_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node8
  · exact profile24_node9
  · exact profile24_node10

def profile24_node11_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 29 25 25), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile24_node11 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,28] 3 profile24_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22,28] 3 profile24_node11_cert).mp (by decide +kernel))

def profile24_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node4 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile24_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [22] (choices 3) [13,21,25,28] profile24_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node5
  · exact profile24_node6
  · exact profile24_node7
  · exact profile24_node11

def profile24_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile24_node13 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,13] 3 profile24_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,13] 3 profile24_node13_cert).mp (by decide +kernel))

def profile24_node14_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 31 27 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile24_node14 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,21] 3 profile24_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,21] 3 profile24_node14_cert).mp (by decide +kernel))

def profile24_node15_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 23 27 19), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile24_node15 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,28] 3 profile24_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28,28] 3 profile24_node15_cert).mp (by decide +kernel))

def profile24_node12_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile24_node12 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28] 3 (by decide) (choices 3) [13,21,28] profile24_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [28] (choices 3) [13,21,28] profile24_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node13
  · exact profile24_node14
  · exact profile24_node15

def profile24_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile24_node0 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [] 3 (by decide) (choices 3) [14,22,28] profile24_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [] (choices 3) [14,22,28] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node1
  · exact profile24_node4
  · exact profile24_node12

theorem profile24 : Upper (D (n:=5) [51,49,34,34,19]) (R (n:=5) [51,49,34,34,19]) [] 3 := profile24_node0

def profile25_node3_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 15 23 21 26 26), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile25_node3 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,17] 3 profile25_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,17] 3 profile25_node3_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 15 23 22 25 25), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile25_node4 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,18] 3 profile25_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,18] 3 profile25_node4_cert).mp (by decide +kernel))

def profile25_node6_cert : CutBound 5 := { lost := (rows 0 0 3 2 0), upper := (rows 15 23 28 25 18), lower := (rows 15 23 28 25 16), losses := [{ target := 0, region := (rows 0 2 13 8 19), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 14 10 16), good := (rows 13 29 28 29 16) }] }

theorem profile25_node6 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,17] 3 profile25_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,17] 3 profile25_node6_cert).mp (by decide +kernel))

def profile25_node7_cert : CutBound 5 := { lost := (rows 0 0 3 1 0), upper := (rows 15 23 28 26 17), lower := (rows 15 23 28 26 16), losses := [{ target := 0, region := (rows 0 2 14 10 16), good := (rows 14 30 28 30 16) },{ target := 1, region := (rows 1 0 13 8 19), good := (rows 29 21 28 28 16) }] }

theorem profile25_node7 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,18] 3 profile25_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24,18] 3 profile25_node7_cert).mp (by decide +kernel))

def profile25_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node5 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24] 3 (by decide) (choices 2) [17,18] profile25_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21,24] (choices 2) [17,18] profile25_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node6
  · exact profile25_node7

def profile25_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node2 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21] 3 (by decide) (choices 2) [17,18,24] profile25_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,21] (choices 2) [17,18,24] profile25_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node3
  · exact profile25_node4
  · exact profile25_node5

def profile25_node8_cert : CutBound 5 := { lost := (rows 16 0 8 4 0), upper := (rows 15 30 23 27 19), lower := (rows 15 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile25_node8 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,28] 3 profile25_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14,28] 3 profile25_node8_cert).mp (by decide +kernel))

def profile25_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile25_node1 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14] 3 (by decide) (choices 3) [21,28] profile25_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [14] (choices 3) [21,28] profile25_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node2
  · exact profile25_node8

def profile25_node11_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 23 15 21 26 26), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile25_node11 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,17] 3 profile25_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,17] 3 profile25_node11_cert).mp (by decide +kernel))

def profile25_node12_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 23 15 22 25 25), lower := (rows 23 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile25_node12 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,18] 3 profile25_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,18] 3 profile25_node12_cert).mp (by decide +kernel))

def profile25_node14_cert : CutBound 5 := { lost := (rows 0 0 3 2 0), upper := (rows 23 15 28 25 18), lower := (rows 23 15 28 25 16), losses := [{ target := 0, region := (rows 0 2 14 8 19), good := (rows 22 30 28 28 16) },{ target := 1, region := (rows 1 0 13 9 16), good := (rows 29 13 28 29 16) }] }

theorem profile25_node14 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,17] 3 profile25_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,17] 3 profile25_node14_cert).mp (by decide +kernel))

def profile25_node15_cert : CutBound 5 := { lost := (rows 0 0 3 1 0), upper := (rows 23 15 28 26 17), lower := (rows 23 15 28 26 16), losses := [{ target := 0, region := (rows 0 2 13 9 16), good := (rows 30 14 28 30 16) },{ target := 1, region := (rows 1 0 14 8 19), good := (rows 21 29 28 28 16) }] }

theorem profile25_node15 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,18] 3 profile25_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24,18] 3 profile25_node15_cert).mp (by decide +kernel))

def profile25_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node13 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24] 3 (by decide) (choices 2) [17,18] profile25_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13,24] (choices 2) [17,18] profile25_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node14
  · exact profile25_node15

def profile25_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node10 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13] 3 (by decide) (choices 2) [17,18,24] profile25_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,13] (choices 2) [17,18,24] profile25_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node11
  · exact profile25_node12
  · exact profile25_node13

def profile25_node16_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile25_node16 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,21] 3 profile25_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,21] 3 profile25_node16_cert).mp (by decide +kernel))

def profile25_node18_cert : CutBound 5 := { lost := (rows 8 0 8 3 0), upper := (rows 23 27 7 28 28), lower := (rows 23 27 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile25_node18 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,3] 3 profile25_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,3] 3 profile25_node18_cert).mp (by decide +kernel))

def profile25_node19_cert : CutBound 5 := { lost := (rows 0 0 18 1 0), upper := (rows 23 27 13 30 22), lower := (rows 23 27 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 13 8 16) },{ target := 4, region := (rows 1 2 6 8 0), good := (rows 7 15 13 8 0) }] }

theorem profile25_node19 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,9] 3 profile25_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,9] 3 profile25_node19_cert).mp (by decide +kernel))

def profile25_node20_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 14 29 21), lower := (rows 23 27 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile25_node20 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,10] 3 profile25_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,10] 3 profile25_node20_cert).mp (by decide +kernel))

def profile25_node21_cert : CutBound 5 := { lost := (rows 8 0 10 1 0), upper := (rows 23 27 21 14 30), lower := (rows 23 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 21 29 21 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 21 0 16) }] }

theorem profile25_node21 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,17] 3 profile25_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,17] 3 profile25_node21_cert).mp (by decide +kernel))

def profile25_node22_cert : CutBound 5 := { lost := (rows 8 0 9 2 0), upper := (rows 23 27 22 13 29), lower := (rows 23 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile25_node22 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,18] 3 profile25_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,18] 3 profile25_node22_cert).mp (by decide +kernel))

def profile25_node23_cert : CutBound 5 := { lost := (rows 0 0 3 16 0), upper := (rows 23 27 28 15 23), lower := (rows 23 27 28 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 28 8 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile25_node23 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,24] 3 profile25_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25,24] 3 profile25_node23_cert).mp (by decide +kernel))

def profile25_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node17 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile25_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,25] (choices 2) [3,9,10,17,18,24] profile25_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node18
  · exact profile25_node19
  · exact profile25_node20
  · exact profile25_node21
  · exact profile25_node22
  · exact profile25_node23

def profile25_node25_cert : CutBound 5 := { lost := (rows 8 0 8 6 0), upper := (rows 23 30 7 25 25), lower := (rows 23 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile25_node25 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,3] 3 profile25_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,3] 3 profile25_node25_cert).mp (by decide +kernel))

def profile25_node27_cert : CutBound 5 := { lost := (rows 0 1 2 2 0), upper := (rows 23 30 13 25 18), lower := (rows 23 30 13 25 16), losses := [{ target := 0, region := (rows 0 6 4 8 23), good := (rows 22 30 30 24 16) },{ target := 1, region := (rows 1 0 13 9 16), good := (rows 29 28 13 29 16) }] }

theorem profile25_node27 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,17] 3 profile25_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,17] 3 profile25_node27_cert).mp (by decide +kernel))

def profile25_node28_cert : CutBound 5 := { lost := (rows 0 1 0 5 0), upper := (rows 23 30 13 26 17), lower := (rows 23 30 13 26 16), losses := [{ target := 0, region := (rows 0 3 4 11 16), good := (rows 30 30 14 26 16) },{ target := 2, region := (rows 1 2 0 11 21), good := (rows 27 26 25 26 16) }] }

theorem profile25_node28 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,18] 3 profile25_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9,18] 3 profile25_node28_cert).mp (by decide +kernel))

def profile25_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node26 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9] 3 (by decide) (choices 2) [17,18] profile25_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,9] (choices 2) [17,18] profile25_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node27
  · exact profile25_node28

def profile25_node29_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 23 30 14 25 17), lower := (rows 23 30 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 10 8 16) }] }

theorem profile25_node29 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,10] 3 profile25_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,10] 3 profile25_node29_cert).mp (by decide +kernel))

def profile25_node30_cert : CutBound 5 := { lost := (rows 8 0 10 4 0), upper := (rows 23 30 21 11 27), lower := (rows 23 30 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 28 21 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 7 0 16), good := (rows 23 23 21 0 16) }] }

theorem profile25_node30 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,17] 3 profile25_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,17] 3 profile25_node30_cert).mp (by decide +kernel))

def profile25_node31_cert : CutBound 5 := { lost := (rows 0 0 1 6 0), upper := (rows 23 30 22 9 25), lower := (rows 23 30 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 18 8 16) }] }

theorem profile25_node31 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,18] 3 profile25_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,18] 3 profile25_node31_cert).mp (by decide +kernel))

def profile25_node32_cert : CutBound 5 := { lost := (rows 0 1 3 0 0), upper := (rows 23 30 28 11 19), lower := (rows 23 30 28 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 28 28 8 16) }] }

theorem profile25_node32 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,24] 3 profile25_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28,24] 3 profile25_node32_cert).mp (by decide +kernel))

def profile25_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node24 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile25_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22,28] (choices 2) [3,9,10,17,18,24] profile25_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node25
  · exact profile25_node26
  · exact profile25_node29
  · exact profile25_node30
  · exact profile25_node31
  · exact profile25_node32

def profile25_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node9 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile25_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [22] (choices 3) [13,21,25,28] profile25_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile25_node10
  · exact profile25_node16
  · exact profile25_node17
  · exact profile25_node24

def profile25_node34_cert : CutBound 5 := { lost := (rows 0 16 8 4 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile25_node34 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,13] 3 profile25_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,13] 3 profile25_node34_cert).mp (by decide +kernel))

def profile25_node36_cert : CutBound 5 := { lost := (rows 0 8 8 5 0), upper := (rows 29 23 7 26 26), lower := (rows 29 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) },{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 7 0 16) }] }

theorem profile25_node36 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,3] 3 profile25_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,3] 3 profile25_node36_cert).mp (by decide +kernel))

def profile25_node37_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 29 23 13 26 18), lower := (rows 29 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 12 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 13 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 9 8 16) }] }

theorem profile25_node37 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,9] 3 profile25_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,9] 3 profile25_node37_cert).mp (by decide +kernel))

def profile25_node39_cert : CutBound 5 := { lost := (rows 2 0 0 6 0), upper := (rows 29 23 14 25 18), lower := (rows 29 23 14 25 16), losses := [{ target := 1, region := (rows 3 0 4 11 16), good := (rows 29 29 13 25 16) },{ target := 2, region := (rows 1 2 0 11 22), good := (rows 25 27 26 25 16) }] }

theorem profile25_node39 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,17] 3 profile25_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,17] 3 profile25_node39_cert).mp (by decide +kernel))

def profile25_node40_cert : CutBound 5 := { lost := (rows 2 0 1 1 0), upper := (rows 29 23 14 26 17), lower := (rows 29 23 14 26 16), losses := [{ target := 0, region := (rows 0 2 14 10 16), good := (rows 28 30 14 30 16) },{ target := 1, region := (rows 5 0 4 8 23), good := (rows 29 21 29 24 16) }] }

theorem profile25_node40 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,18] 3 profile25_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10,18] 3 profile25_node40_cert).mp (by decide +kernel))

def profile25_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node38 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10] 3 (by decide) (choices 2) [17,18] profile25_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,10] (choices 2) [17,18] profile25_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node39
  · exact profile25_node40

def profile25_node41_cert : CutBound 5 := { lost := (rows 0 0 2 5 0), upper := (rows 29 23 21 10 26), lower := (rows 29 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 17 8 16) }] }

theorem profile25_node41 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,17] 3 profile25_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,17] 3 profile25_node41_cert).mp (by decide +kernel))

def profile25_node42_cert : CutBound 5 := { lost := (rows 0 8 9 4 0), upper := (rows 29 23 22 11 27), lower := (rows 29 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 22 22 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 26 8 16) },{ target := 3, region := (rows 1 3 7 0 16), good := (rows 23 23 22 0 16) }] }

theorem profile25_node42 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,18] 3 profile25_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,18] 3 profile25_node42_cert).mp (by decide +kernel))

def profile25_node43_cert : CutBound 5 := { lost := (rows 2 0 3 0 0), upper := (rows 29 23 28 11 19), lower := (rows 29 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 28 22 28 8 16) },{ target := 1, region := (rows 5 0 5 8 16), good := (rows 29 21 29 8 16) }] }

theorem profile25_node43 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,24] 3 profile25_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21,24] 3 profile25_node43_cert).mp (by decide +kernel))

def profile25_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node35 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile25_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,21] (choices 2) [3,9,10,17,18,24] profile25_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node36
  · exact profile25_node37
  · exact profile25_node38
  · exact profile25_node41
  · exact profile25_node42
  · exact profile25_node43

def profile25_node45_cert : CutBound 5 := { lost := (rows 2 1 0 4 0), upper := (rows 29 30 7 27 19), lower := (rows 29 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 5 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile25_node45 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,3] 3 profile25_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,3] 3 profile25_node45_cert).mp (by decide +kernel))

def profile25_node46_cert : CutBound 5 := { lost := (rows 2 1 2 0 0), upper := (rows 29 30 21 11 19), lower := (rows 29 30 21 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 3 0 7 8 16), good := (rows 29 29 21 8 16) }] }

theorem profile25_node46 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,17] 3 profile25_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,17] 3 profile25_node46_cert).mp (by decide +kernel))

def profile25_node47_cert : CutBound 5 := { lost := (rows 2 1 1 0 0), upper := (rows 29 30 22 11 19), lower := (rows 29 30 22 8 16), losses := [{ target := 0, region := (rows 0 3 7 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 21 8 16) }] }

theorem profile25_node47 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,18] 3 profile25_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28,18] 3 profile25_node47_cert).mp (by decide +kernel))

def profile25_node44_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node44 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28] 3 (by decide) (choices 2) [3,17,18] profile25_node44_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28,28] (choices 2) [3,17,18] profile25_node44_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node45
  · exact profile25_node46
  · exact profile25_node47

def profile25_node33_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile25_node33 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28] 3 (by decide) (choices 3) [13,21,28] profile25_node33_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [28] (choices 3) [13,21,28] profile25_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node34
  · exact profile25_node35
  · exact profile25_node44

def profile25_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile25_node0 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [] 3 (by decide) (choices 3) [14,22,28] profile25_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [] (choices 3) [14,22,28] profile25_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node1
  · exact profile25_node9
  · exact profile25_node33

theorem profile25 : Upper (D (n:=5) [50,50,34,34,19]) (R (n:=5) [50,50,34,34,19]) [] 3 := profile25_node0

def profile26_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 23 21 28 28), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile26_node3 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,17] 3 profile26_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,17] 3 profile26_node3_cert).mp (by decide +kernel))

def profile26_node4_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 23 28 29 21), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile26_node4 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,24] 3 profile26_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21,24] 3 profile26_node4_cert).mp (by decide +kernel))

def profile26_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node2 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21] 3 (by decide) (choices 2) [17,24] profile26_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,21] (choices 2) [17,24] profile26_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node3
  · exact profile26_node4

def profile26_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 21 29 21), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile26_node5 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,25] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,25] 3 profile26_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,25] 3 profile26_node5_cert).mp (by decide +kernel))

def profile26_node6_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 30 21 29 21), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile26_node6 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,28] 3 profile26_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14,28] 3 profile26_node6_cert).mp (by decide +kernel))

def profile26_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14] 3 (by decide) (choices 3) [21,25,28] profile26_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [14] (choices 3) [21,25,28] profile26_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node2
  · exact profile26_node5
  · exact profile26_node6

def profile26_node9_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 15 21 28 28), lower := (rows 23 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile26_node9 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,17] 3 profile26_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,17] 3 profile26_node9_cert).mp (by decide +kernel))

def profile26_node10_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 15 28 29 21), lower := (rows 23 15 28 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile26_node10 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,24] 3 profile26_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13,24] 3 profile26_node10_cert).mp (by decide +kernel))

def profile26_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node8 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13] 3 (by decide) (choices 2) [17,24] profile26_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,13] (choices 2) [17,24] profile26_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node9
  · exact profile26_node10

def profile26_node11_cert : CutBound 5 := { lost := (rows 8 8 0 0 0), upper := (rows 23 23 29 29 29), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile26_node11 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,21] 3 profile26_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,21] 3 profile26_node11_cert).mp (by decide +kernel))

def profile26_node13_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 13 28 20), lower := (rows 23 27 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 28 8 16) }] }

theorem profile26_node13 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,9] 3 profile26_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,9] 3 profile26_node13_cert).mp (by decide +kernel))

def profile26_node14_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 21 12 28), lower := (rows 23 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 28 8 16) }] }

theorem profile26_node14 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,17] 3 profile26_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,17] 3 profile26_node14_cert).mp (by decide +kernel))

def profile26_node15_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 28 13 21), lower := (rows 23 27 28 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 28 8 16) }] }

theorem profile26_node15 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,24] 3 profile26_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25,24] 3 profile26_node15_cert).mp (by decide +kernel))

def profile26_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node12 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25] 3 (by decide) (choices 2) [9,17,24] profile26_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,25] (choices 2) [9,17,24] profile26_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node13
  · exact profile26_node14
  · exact profile26_node15

def profile26_node16_cert : CutBound 5 := { lost := (rows 8 0 0 0 0), upper := (rows 23 30 29 29 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile26_node16 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,28] 3 profile26_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22,28] 3 profile26_node16_cert).mp (by decide +kernel))

def profile26_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node7 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22] 3 (by decide) (choices 3) [13,21,25,28] profile26_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [22] (choices 3) [13,21,25,28] profile26_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile26_node8
  · exact profile26_node11
  · exact profile26_node12
  · exact profile26_node16

def profile26_node18_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 21 29 21), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile26_node18 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,13] 3 profile26_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,13] 3 profile26_node18_cert).mp (by decide +kernel))

def profile26_node20_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 13 28 20), lower := (rows 27 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 28 8 16) }] }

theorem profile26_node20 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,9] 3 profile26_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,9] 3 profile26_node20_cert).mp (by decide +kernel))

def profile26_node21_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 21 12 28), lower := (rows 27 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 28 8 16) }] }

theorem profile26_node21 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,17] 3 profile26_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,17] 3 profile26_node21_cert).mp (by decide +kernel))

def profile26_node22_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 28 13 21), lower := (rows 27 23 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 28 8 16) }] }

theorem profile26_node22 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,24] 3 profile26_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21,24] 3 profile26_node22_cert).mp (by decide +kernel))

def profile26_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node19 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21] 3 (by decide) (choices 2) [9,17,24] profile26_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,21] (choices 2) [9,17,24] profile26_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node20
  · exact profile26_node21
  · exact profile26_node22

def profile26_node23_cert : CutBound 5 := { lost := (rows 4 0 0 0 0), upper := (rows 27 30 21 29 21), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile26_node23 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,28] 3 profile26_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26,28] 3 profile26_node23_cert).mp (by decide +kernel))

def profile26_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node17 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26] 3 (by decide) (choices 3) [13,21,28] profile26_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [26] (choices 3) [13,21,28] profile26_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node18
  · exact profile26_node19
  · exact profile26_node23

def profile26_node25_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 15 23 31 23), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile26_node25 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,13] 3 profile26_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,13] 3 profile26_node25_cert).mp (by decide +kernel))

def profile26_node26_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 29 23 31 31 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile26_node26 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,21] 3 profile26_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,21] 3 profile26_node26_cert).mp (by decide +kernel))

def profile26_node27_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 29 27 23 31 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile26_node27 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,25] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,25] 3 profile26_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,25] 3 profile26_node27_cert).mp (by decide +kernel))

def profile26_node28_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 23 31 23), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile26_node28 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,28] 3 profile26_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28,28] 3 profile26_node28_cert).mp (by decide +kernel))

def profile26_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node24 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28] 3 (by decide) (choices 3) [13,21,25,28] profile26_node24_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [28] (choices 3) [13,21,25,28] profile26_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile26_node25
  · exact profile26_node26
  · exact profile26_node27
  · exact profile26_node28

def profile26_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node0 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [] 3 := by
  apply routed_branch (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [] 3 (by decide) (choices 3) [14,22,26,28] profile26_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [] (choices 3) [14,22,26,28] profile26_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile26_node1
  · exact profile26_node7
  · exact profile26_node17
  · exact profile26_node24

theorem profile26 : Upper (D (n:=5) [50,49,35,34,19]) (R (n:=5) [50,49,35,34,19]) [] 3 := profile26_node0

def profile27_node2_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 23 31 23), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile27_node2 : Upper (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,17] 3 profile27_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,17] 3 profile27_node2_cert).mp (by decide +kernel))

def profile27_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 22 23 27 19), lower := (rows 31 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 4 8 16) }] }

theorem profile27_node3 : Upper (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,20] 3 profile27_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30,20] 3 profile27_node3_cert).mp (by decide +kernel))

def profile27_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30] 3 (by decide) (choices 2) [17,20] profile27_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [30] (choices 2) [17,20] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile27_node2
  · exact profile27_node3

def profile27_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [] 3 (by decide) (choices 4) [30] profile27_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [] (choices 4) [30] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=5) [66,34,34,33,20]) (R (n:=5) [66,34,34,33,20]) [] 3 := profile27_node0

def profile28_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile28_node2 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,21] 3 profile28_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,21] 3 profile28_node2_cert).mp (by decide +kernel))

def profile28_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 21 30 22), lower := (rows 23 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile28_node4 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,17] 3 profile28_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,17] 3 profile28_node4_cert).mp (by decide +kernel))

def profile28_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 22 29 21), lower := (rows 23 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 22 30 22 8 16) }] }

theorem profile28_node5 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,18] 3 profile28_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25,18] 3 profile28_node5_cert).mp (by decide +kernel))

def profile28_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node3 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25] 3 (by decide) (choices 2) [17,18] profile28_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,25] (choices 2) [17,18] profile28_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node4
  · exact profile28_node5

def profile28_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 23 27 19), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile28_node6 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,28] 3 profile28_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22,28] 3 profile28_node6_cert).mp (by decide +kernel))

def profile28_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node1 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22] 3 (by decide) (choices 3) [21,25,28] profile28_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [22] (choices 3) [21,25,28] profile28_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile28_node2
  · exact profile28_node3
  · exact profile28_node6

def profile28_node9_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 21 30 22), lower := (rows 27 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) }] }

theorem profile28_node9 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,17] 3 profile28_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,17] 3 profile28_node9_cert).mp (by decide +kernel))

def profile28_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 22 29 21), lower := (rows 27 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile28_node10 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,18] 3 profile28_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21,18] 3 profile28_node10_cert).mp (by decide +kernel))

def profile28_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node8 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21] 3 (by decide) (choices 2) [17,18] profile28_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26,21] (choices 2) [17,18] profile28_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node9
  · exact profile28_node10

def profile28_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node7 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26] 3 (by decide) (choices 3) [21] profile28_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [26] (choices 3) [21] profile28_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node8

def profile28_node12_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 23 27 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile28_node12 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28,21] 3 profile28_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28,21] 3 profile28_node12_cert).mp (by decide +kernel))

def profile28_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node11 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28] 3 (by decide) (choices 3) [21] profile28_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [28] (choices 3) [21] profile28_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node12

def profile28_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [] 3 (by decide) (choices 3) [22,26,28] profile28_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [] (choices 3) [22,26,28] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile28_node1
  · exact profile28_node7
  · exact profile28_node11

theorem profile28 : Upper (D (n:=5) [50,50,34,33,20]) (R (n:=5) [50,50,34,33,20]) [] 3 := profile28_node0

def profile29_node2_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 19 30 30 30), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) }] }

theorem profile29_node2 : Upper (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,17] 3 :=
  cut_bound_sound (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,17] 3 profile29_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,17] 3 profile29_node2_cert).mp (by decide +kernel))

def profile29_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 22 31 27 27), lower := (rows 31 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile29_node3 : Upper (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,20] 3 :=
  cut_bound_sound (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,20] 3 profile29_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30,20] 3 profile29_node3_cert).mp (by decide +kernel))

def profile29_node1_route : Route 5 := (fun mask => match mask with | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile29_node1 : Upper (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30] 3 := by
  apply routed_branch (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30] 3 (by decide) (choices 2) [17,20] profile29_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [30] (choices 2) [17,20] profile29_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node2
  · exact profile29_node3

def profile29_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node0 : Upper (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [] 3 := by
  apply routed_branch (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [] 3 (by decide) (choices 4) [30] profile29_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [] (choices 4) [30] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node1

theorem profile29 : Upper (D (n:=5) [65,34,34,34,20]) (R (n:=5) [65,34,34,34,20]) [] 3 := profile29_node0

def profile30_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 29 25 25), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile30_node2 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,21] 3 profile30_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,21] 3 profile30_node2_cert).mp (by decide +kernel))

def profile30_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 21 28 28), lower := (rows 23 27 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 28 8 16) }] }

theorem profile30_node4 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,17] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,17] 3 profile30_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,17] 3 profile30_node4_cert).mp (by decide +kernel))

def profile30_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 28 29 21), lower := (rows 23 27 28 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 28 8 16) }] }

theorem profile30_node5 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,24] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,24] 3 profile30_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25,24] 3 profile30_node5_cert).mp (by decide +kernel))

def profile30_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node3 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25] 3 := by
  apply routed_branch (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25] 3 (by decide) (choices 2) [17,24] profile30_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,25] (choices 2) [17,24] profile30_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node4
  · exact profile30_node5

def profile30_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 30 29 25 25), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile30_node6 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,28] 3 profile30_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22,28] 3 profile30_node6_cert).mp (by decide +kernel))

def profile30_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node1 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22] 3 (by decide) (choices 3) [21,25,28] profile30_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [22] (choices 3) [21,25,28] profile30_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node2
  · exact profile30_node3
  · exact profile30_node6

def profile30_node8_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 23 31 27 27), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile30_node8 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,21] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,21] 3 profile30_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,21] 3 profile30_node8_cert).mp (by decide +kernel))

def profile30_node9_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 23 27 19), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile30_node9 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,28] 3 profile30_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28,28] 3 profile30_node9_cert).mp (by decide +kernel))

def profile30_node7_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile30_node7 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28] 3 (by decide) (choices 3) [21,28] profile30_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [28] (choices 3) [21,28] profile30_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node8
  · exact profile30_node9

def profile30_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile30_node0 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [] 3 := by
  apply routed_branch (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [] 3 (by decide) (choices 3) [22,28] profile30_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [] (choices 3) [22,28] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile30_node1
  · exact profile30_node7

theorem profile30 : Upper (D (n:=5) [50,49,34,34,20]) (R (n:=5) [50,49,34,34,20]) [] 3 := profile30_node0

def profile31_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile31_node2 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,5] 3 profile31_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,5] 3 profile31_node2_cert).mp (by decide +kernel))

def profile31_node4_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 19 7 13 29), lower := (rows 15 19 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile31_node4 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,3] 3 profile31_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,3] 3 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 19 13 15 23), lower := (rows 15 19 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile31_node5 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,9] 3 profile31_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17,9] 3 profile31_node5_cert).mp (by decide +kernel))

def profile31_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node3 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17] 3 (by decide) (choices 2) [3,9] profile31_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14,17] (choices 2) [3,9] profile31_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node4
  · exact profile31_node5

def profile31_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile31_node1 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14] 3 := by
  apply routed_branch (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14] 3 (by decide) (choices 2) [5,17] profile31_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [14] (choices 2) [5,17] profile31_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node2
  · exact profile31_node3

def profile31_node7_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 23 7 15 11 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile31_node7 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,5] 3 profile31_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,5] 3 profile31_node7_cert).mp (by decide +kernel))

def profile31_node9_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 23 11 7 13 29), lower := (rows 23 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile31_node9 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,3] 3 profile31_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,3] 3 profile31_node9_cert).mp (by decide +kernel))

def profile31_node10_cert : CutBound 5 := { lost := (rows 0 4 2 0 8), upper := (rows 23 11 13 15 23), lower := (rows 23 11 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 11 11 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) }] }

theorem profile31_node10 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,9] 3 profile31_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9,9] 3 profile31_node10_cert).mp (by decide +kernel))

def profile31_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node8 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9] 3 (by decide) (choices 2) [3,9] profile31_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22,9] (choices 2) [3,9] profile31_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node9
  · exact profile31_node10

def profile31_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node6 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22] 3 := by
  apply routed_branch (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22] 3 (by decide) (choices 2) [5,9] profile31_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [22] (choices 2) [5,9] profile31_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node7
  · exact profile31_node8

def profile31_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile31_node0 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [] 3 := by
  apply routed_branch (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [] 3 (by decide) (choices 3) [14,22] profile31_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [] (choices 3) [14,22] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node1
  · exact profile31_node6

theorem profile31 : Upper (D (n:=5) [52,34,34,34,33]) (R (n:=5) [52,34,34,34,33]) [] 3 := profile31_node0

def profile32_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile32_node2 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,5] 3 profile32_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,5] 3 profile32_node2_cert).mp (by decide +kernel))

def profile32_node3_cert : CutBound 5 := { lost := (rows 0 1 0 4 4), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile32_node3 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,12] 3 profile32_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,12] 3 profile32_node3_cert).mp (by decide +kernel))

def profile32_node6_cert : CutBound 5 := { lost := (rows 0 0 0 4 3), upper := (rows 15 19 7 11 28), lower := (rows 15 19 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 11 27 11 11 16) }] }

theorem profile32_node6 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,3] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,3] 3 profile32_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,3] 3 profile32_node6_cert).mp (by decide +kernel))

def profile32_node7_cert : CutBound 5 := { lost := (rows 0 4 0 2 5), upper := (rows 15 19 7 13 26), lower := (rows 15 19 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 13 13 16) },{ target := 2, region := (rows 1 15 0 8 25), good := (rows 27 19 19 27 16) }] }

theorem profile32_node7 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,5] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,5] 3 profile32_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,5] 3 profile32_node7_cert).mp (by decide +kernel))

def profile32_node8_cert : CutBound 5 := { lost := (rows 0 4 0 1 6), upper := (rows 15 19 7 14 25), lower := (rows 15 19 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 21 12 16) },{ target := 2, region := (rows 1 7 0 8 17), good := (rows 27 19 19 10 16) }] }

theorem profile32_node8 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,6] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,6] 3 profile32_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3,6] 3 profile32_node8_cert).mp (by decide +kernel))

def profile32_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node5 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3] 3 (by decide) (choices 2) [3,5,6] profile32_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,3] (choices 2) [3,5,6] profile32_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node6
  · exact profile32_node7
  · exact profile32_node8

def profile32_node9_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 19 13 15 23), lower := (rows 15 19 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile32_node9 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,9] 3 profile32_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,9] 3 profile32_node9_cert).mp (by decide +kernel))

def profile32_node10_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 19 14 15 23), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 0 16) }] }

theorem profile32_node10 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,10] 3 profile32_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17,10] 3 profile32_node10_cert).mp (by decide +kernel))

def profile32_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node4 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17] 3 (by decide) (choices 2) [3,9,10] profile32_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,17] (choices 2) [3,9,10] profile32_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node5
  · exact profile32_node9
  · exact profile32_node10

def profile32_node12_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 15 22 7 11 27), lower := (rows 15 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile32_node12 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,3] 3 profile32_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,3] 3 profile32_node12_cert).mp (by decide +kernel))

def profile32_node13_cert : CutBound 5 := { lost := (rows 0 0 2 4 4), upper := (rows 15 22 13 11 19), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) }] }

theorem profile32_node13 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,9] 3 profile32_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20,9] 3 profile32_node13_cert).mp (by decide +kernel))

def profile32_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node11 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20] 3 (by decide) (choices 2) [3,9] profile32_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14,20] (choices 2) [3,9] profile32_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile32_node12
  · exact profile32_node13

def profile32_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile32_node1 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile32_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [14] (choices 2) [5,12,17,20] profile32_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile32_node2
  · exact profile32_node3
  · exact profile32_node4
  · exact profile32_node11

def profile32_node15_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 23 7 15 11 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile32_node15 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,5] 3 profile32_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,5] 3 profile32_node15_cert).mp (by decide +kernel))

def profile32_node18_cert : CutBound 5 := { lost := (rows 0 4 8 4 0), upper := (rows 23 11 7 11 28), lower := (rows 23 11 7 11 16), losses := [{ target := 2, region := (rows 1 15 0 15 16), good := (rows 27 11 11 11 16) },{ target := 3, region := (rows 1 2 15 0 16), good := (rows 23 7 7 7 16) }] }

theorem profile32_node18 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,3] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,3] 3 profile32_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,3] 3 profile32_node18_cert).mp (by decide +kernel))

def profile32_node19_cert : CutBound 5 := { lost := (rows 0 4 0 2 5), upper := (rows 23 11 7 13 26), lower := (rows 23 11 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 26 22 12 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 9 13 13 16) },{ target := 2, region := (rows 1 10 0 8 26), good := (rows 19 27 19 27 16) }] }

theorem profile32_node19 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,5] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,5] 3 profile32_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,5] 3 profile32_node19_cert).mp (by decide +kernel))

def profile32_node20_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 23 11 7 14 25), lower := (rows 23 11 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 10 14 14 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 25 21 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 26 16) }] }

theorem profile32_node20 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,6] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,6] 3 profile32_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3,6] 3 profile32_node20_cert).mp (by decide +kernel))

def profile32_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node17 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3] 3 (by decide) (choices 2) [3,5,6] profile32_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,3] (choices 2) [3,5,6] profile32_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node18
  · exact profile32_node19
  · exact profile32_node20

def profile32_node21_cert : CutBound 5 := { lost := (rows 0 4 2 0 8), upper := (rows 23 11 13 15 23), lower := (rows 23 11 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 11 11 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) }] }

theorem profile32_node21 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,9] 3 profile32_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,9] 3 profile32_node21_cert).mp (by decide +kernel))

def profile32_node22_cert : CutBound 5 := { lost := (rows 8 0 1 0 8), upper := (rows 23 11 14 15 23), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile32_node22 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,10] 3 profile32_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9,10] 3 profile32_node22_cert).mp (by decide +kernel))

def profile32_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node16 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9] 3 (by decide) (choices 2) [3,9,10] profile32_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,9] (choices 2) [3,9,10] profile32_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node17
  · exact profile32_node21
  · exact profile32_node22

def profile32_node24_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 23 14 7 11 27), lower := (rows 23 14 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) }] }

theorem profile32_node24 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,3] 3 profile32_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,3] 3 profile32_node24_cert).mp (by decide +kernel))

def profile32_node25_cert : CutBound 5 := { lost := (rows 0 1 0 4 4), upper := (rows 23 14 13 11 19), lower := (rows 23 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 14 14 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) }] }

theorem profile32_node25 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,9] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,9] 3 profile32_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12,9] 3 profile32_node25_cert).mp (by decide +kernel))

def profile32_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node23 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12] 3 (by decide) (choices 2) [3,9] profile32_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22,12] (choices 2) [3,9] profile32_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile32_node24
  · exact profile32_node25

def profile32_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node14 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22] 3 (by decide) (choices 2) [5,9,12] profile32_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [22] (choices 2) [5,9,12] profile32_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node15
  · exact profile32_node16
  · exact profile32_node23

def profile32_node27_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 29 7 15 11 27), lower := (rows 29 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile32_node27 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,5] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,5] 3 profile32_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,5] 3 profile32_node27_cert).mp (by decide +kernel))

def profile32_node29_cert : CutBound 5 := { lost := (rows 0 1 0 4 4), upper := (rows 29 14 7 11 19), lower := (rows 29 14 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 6 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile32_node29 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12,3] 3 :=
  cut_bound_sound (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12,3] 3 profile32_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12,3] 3 profile32_node29_cert).mp (by decide +kernel))

def profile32_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node28 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12] 3 (by decide) (choices 2) [3] profile32_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28,12] (choices 2) [3] profile32_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node29

def profile32_node26_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile32_node26 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28] 3 (by decide) (choices 2) [5,12] profile32_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [28] (choices 2) [5,12] profile32_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile32_node27
  · exact profile32_node28

def profile32_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile32_node0 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [] 3 := by
  apply routed_branch (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [] 3 (by decide) (choices 3) [14,22,28] profile32_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [] (choices 3) [14,22,28] profile32_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node1
  · exact profile32_node14
  · exact profile32_node26

theorem profile32 : Upper (D (n:=5) [51,35,34,34,33]) (R (n:=5) [51,35,34,34,33]) [] 3 := profile32_node0

#print axioms profile32
end Delivery.FiveVertexPositive11
