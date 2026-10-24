import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile87_node2_cert : CutBound 5 := { lost := (rows 16 16 8 0 8), upper := (rows 15 15 21 29 21), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile87_node2 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,13] 2 profile87_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,13] 2 profile87_node2_cert).mp (by decide +kernel))

def profile87_node4_cert : CutBound 5 := { lost := (rows 0 8 16 0 8), upper := (rows 15 23 13 29 21), lower := (rows 15 23 13 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile87_node4 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,9] 2 profile87_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,9] 2 profile87_node4_cert).mp (by decide +kernel))

def profile87_node5_cert : CutBound 5 := { lost := (rows 16 8 8 16 0), upper := (rows 15 23 21 13 29), lower := (rows 15 23 21 8 16), losses := [{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 8 0) }] }

theorem profile87_node5 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,17] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,17] 2 profile87_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21,17] 2 profile87_node5_cert).mp (by decide +kernel))

def profile87_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node3 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21] 2 (by decide) (choices 2) [9,17] profile87_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,21] (choices 2) [9,17] profile87_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile87_node4
  · exact profile87_node5

def profile87_node7_cert : CutBound 5 := { lost := (rows 0 0 8 16 8), upper := (rows 15 27 21 13 21), lower := (rows 15 27 21 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 15 11 13 8 0) }] }

theorem profile87_node7 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25,17] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25,17] 2 profile87_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25,17] 2 profile87_node7_cert).mp (by decide +kernel))

def profile87_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node6 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25] 2 (by decide) (choices 2) [17] profile87_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14,25] (choices 2) [17] profile87_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node7

def profile87_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node1 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14] 2 (by decide) (choices 3) [13,21,25] profile87_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [14] (choices 3) [13,21,25] profile87_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node2
  · exact profile87_node3
  · exact profile87_node6

def profile87_node10_cert : CutBound 5 := { lost := (rows 0 16 8 16 8), upper := (rows 27 15 21 13 21), lower := (rows 27 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile87_node10 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13,17] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13,17] 2 profile87_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13,17] 2 profile87_node10_cert).mp (by decide +kernel))

def profile87_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node9 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13] 2 (by decide) (choices 2) [17] profile87_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26,13] (choices 2) [17] profile87_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node10

def profile87_node8_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile87_node8 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26] 2 (by decide) (choices 3) [13] profile87_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [26] (choices 3) [13] profile87_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node9

def profile87_node12_cert : CutBound 5 := { lost := (rows 0 16 8 0 8), upper := (rows 29 15 23 31 23), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile87_node12 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,13] 2 profile87_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,13] 2 profile87_node12_cert).mp (by decide +kernel))

def profile87_node13_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 29 27 7 15 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile87_node13 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,25] 2 profile87_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28,25] 2 profile87_node13_cert).mp (by decide +kernel))

def profile87_node11_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile87_node11 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28] 2 (by decide) (choices 3) [13,25] profile87_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [28] (choices 3) [13,25] profile87_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile87_node12
  · exact profile87_node13

def profile87_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile87_node0 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [] 2 (by decide) (choices 3) [14,26,28] profile87_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [] (choices 3) [14,26,28] profile87_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node1
  · exact profile87_node8
  · exact profile87_node11

theorem profile87 : Upper (D (n:=5) [52,49,35,34,34]) (R (n:=5) [52,49,35,34,34]) [] 2 := profile87_node0

def profile88_node4_cert : CutBound 5 := { lost := (rows 0 0 10 6 9), upper := (rows 15 15 21 25 22), lower := (rows 15 15 21 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 24 16) },{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 13 29 29 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 25 25 16) },{ target := 3, region := (rows 1 2 15 0 19), good := (rows 23 23 21 21 16) }] }

theorem profile88_node4 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,17] 2 profile88_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,17] 2 profile88_node4_cert).mp (by decide +kernel))

def profile88_node5_cert : CutBound 5 := { lost := (rows 16 16 10 0 10), upper := (rows 15 15 21 26 21), lower := (rows 15 15 21 26 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 21 22 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 11 0) }] }

theorem profile88_node5 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,18] 2 profile88_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,18] 2 profile88_node5_cert).mp (by decide +kernel))

def profile88_node6_cert : CutBound 5 := { lost := (rows 16 16 8 3 12), upper := (rows 15 15 21 28 19), lower := (rows 15 15 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 28 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 24 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 20 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile88_node6 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,20] 2 profile88_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17,20] 2 profile88_node6_cert).mp (by decide +kernel))

def profile88_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node3 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17] 2 (by decide) (choices 2) [17,18,20] profile88_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,17] (choices 2) [17,18,20] profile88_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node4
  · exact profile88_node5
  · exact profile88_node6

def profile88_node7_cert : CutBound 5 := { lost := (rows 16 16 8 2 10), upper := (rows 15 15 22 29 21), lower := (rows 15 15 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile88_node7 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,18] 2 profile88_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13,18] 2 profile88_node7_cert).mp (by decide +kernel))

def profile88_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node2 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13] 2 (by decide) (choices 2) [17,18] profile88_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,13] (choices 2) [17,18] profile88_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node3
  · exact profile88_node7

def profile88_node10_cert : CutBound 5 := { lost := (rows 0 8 8 6 3), upper := (rows 15 23 7 25 28), lower := (rows 15 23 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 24 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 25 16) },{ target := 3, region := (rows 1 10 15 0 16), good := (rows 7 23 7 23 16) }] }

theorem profile88_node10 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,17] 2 profile88_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,17] 2 profile88_node10_cert).mp (by decide +kernel))

def profile88_node11_cert : CutBound 5 := { lost := (rows 0 0 24 3 6), upper := (rows 15 23 7 28 25), lower := (rows 15 23 7 28 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 28 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 24 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 20 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 12 0) }] }

theorem profile88_node11 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,20] 2 profile88_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3,20] 2 profile88_node11_cert).mp (by decide +kernel))

def profile88_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node9 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3] 2 (by decide) (choices 2) [17,20] profile88_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,3] (choices 2) [17,20] profile88_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node10
  · exact profile88_node11

def profile88_node13_cert : CutBound 5 := { lost := (rows 0 8 2 6 9), upper := (rows 15 23 13 25 22), lower := (rows 15 23 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 22 28 24 16) },{ target := 1, region := (rows 1 0 15 10 16), good := (rows 13 29 13 29 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 25 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 19 16) }] }

theorem profile88_node13 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,17] 2 profile88_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,17] 2 profile88_node13_cert).mp (by decide +kernel))

def profile88_node14_cert : CutBound 5 := { lost := (rows 0 8 2 5 10), upper := (rows 15 23 13 26 21), lower := (rows 15 23 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 12 26 16) },{ target := 1, region := (rows 1 0 5 8 23), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 26 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 18 16) }] }

theorem profile88_node14 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,18] 2 profile88_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,18] 2 profile88_node14_cert).mp (by decide +kernel))

def profile88_node15_cert : CutBound 5 := { lost := (rows 0 8 2 3 12), upper := (rows 15 23 13 28 19), lower := (rows 15 23 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 12 28 16) },{ target := 1, region := (rows 1 0 7 10 16), good := (rows 13 29 13 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 25 24 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile88_node15 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,20] 2 profile88_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9,20] 2 profile88_node15_cert).mp (by decide +kernel))

def profile88_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node12 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9] 2 (by decide) (choices 2) [17,18,20] profile88_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,9] (choices 2) [17,18,20] profile88_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node13
  · exact profile88_node14
  · exact profile88_node15

def profile88_node16_cert : CutBound 5 := { lost := (rows 16 8 17 2 10), upper := (rows 15 23 14 29 21), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile88_node16 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,10] 2 profile88_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,10] 2 profile88_node16_cert).mp (by decide +kernel))

def profile88_node18_cert : CutBound 5 := { lost := (rows 0 8 10 4 3), upper := (rows 15 23 21 11 28), lower := (rows 15 23 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 20 26 16) },{ target := 1, region := (rows 1 0 15 8 25), good := (rows 29 21 21 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 25 11 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile88_node18 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,3] 2 profile88_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,3] 2 profile88_node18_cert).mp (by decide +kernel))

def profile88_node19_cert : CutBound 5 := { lost := (rows 0 8 10 2 5), upper := (rows 15 23 21 13 26), lower := (rows 15 23 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 20 28 16) },{ target := 1, region := (rows 1 0 6 15 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 17 25 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile88_node19 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,5] 2 profile88_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,5] 2 profile88_node19_cert).mp (by decide +kernel))

def profile88_node20_cert : CutBound 5 := { lost := (rows 0 8 10 1 6), upper := (rows 15 23 21 14 25), lower := (rows 15 23 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 30 28 14 16) },{ target := 1, region := (rows 1 0 7 8 17), good := (rows 29 21 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 17 10 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 6 16) }] }

theorem profile88_node20 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,6] 2 profile88_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17,6] 2 profile88_node20_cert).mp (by decide +kernel))

def profile88_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node17 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17] 2 (by decide) (choices 2) [3,5,6] profile88_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,17] (choices 2) [3,5,6] profile88_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node18
  · exact profile88_node19
  · exact profile88_node20

def profile88_node21_cert : CutBound 5 := { lost := (rows 16 0 9 18 2), upper := (rows 15 23 22 13 29), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile88_node21 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,18] 2 profile88_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,18] 2 profile88_node21_cert).mp (by decide +kernel))

def profile88_node23_cert : CutBound 5 := { lost := (rows 16 8 2 20 10), upper := (rows 15 23 28 11 21), lower := (rows 15 23 28 11 16), losses := [{ target := 1, region := (rows 1 0 13 8 27), good := (rows 29 21 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 19 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 11 0) }] }

theorem profile88_node23 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,3] 2 profile88_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,3] 2 profile88_node23_cert).mp (by decide +kernel))

def profile88_node24_cert : CutBound 5 := { lost := (rows 16 8 2 18 12), upper := (rows 15 23 28 13 19), lower := (rows 15 23 28 13 16), losses := [{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 24 25 16) },{ target := 3, region := (rows 1 11 4 0 27), good := (rows 23 23 22 23 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 13 0) }] }

theorem profile88_node24 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,5] 2 profile88_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24,5] 2 profile88_node24_cert).mp (by decide +kernel))

def profile88_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node22 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24] 2 (by decide) (choices 2) [3,5] profile88_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21,24] (choices 2) [3,5] profile88_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node23
  · exact profile88_node24

def profile88_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node8 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile88_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,21] (choices 2) [3,9,10,17,18,24] profile88_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile88_node9
  · exact profile88_node12
  · exact profile88_node16
  · exact profile88_node17
  · exact profile88_node21
  · exact profile88_node22

def profile88_node26_cert : CutBound 5 := { lost := (rows 16 0 24 2 10), upper := (rows 15 27 7 29 21), lower := (rows 15 27 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile88_node26 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,3] 2 profile88_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,3] 2 profile88_node26_cert).mp (by decide +kernel))

def profile88_node28_cert : CutBound 5 := { lost := (rows 0 0 10 18 9), upper := (rows 15 27 21 13 22), lower := (rows 15 27 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 26 20 28 16) },{ target := 1, region := (rows 1 0 6 15 16), good := (rows 13 29 29 13 16) },{ target := 3, region := (rows 1 2 15 0 19), good := (rows 23 23 21 21 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 15 11 13 13 0) }] }

theorem profile88_node28 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,5] 2 profile88_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,5] 2 profile88_node28_cert).mp (by decide +kernel))

def profile88_node29_cert : CutBound 5 := { lost := (rows 16 0 10 17 10), upper := (rows 15 27 21 14 21), lower := (rows 15 27 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 28 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 21 22 16) },{ target := 4, region := (rows 9 2 4 9 0), good := (rows 15 11 13 15 0) }] }

theorem profile88_node29 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,6] 2 profile88_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17,6] 2 profile88_node29_cert).mp (by decide +kernel))

def profile88_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node27 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17] 2 (by decide) (choices 2) [5,6] profile88_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,17] (choices 2) [5,6] profile88_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node28
  · exact profile88_node29

def profile88_node30_cert : CutBound 5 := { lost := (rows 16 0 9 18 10), upper := (rows 15 27 22 13 21), lower := (rows 15 27 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile88_node30 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,18] 2 profile88_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25,18] 2 profile88_node30_cert).mp (by decide +kernel))

def profile88_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node25 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25] 2 (by decide) (choices 2) [3,17,18] profile88_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,25] (choices 2) [3,17,18] profile88_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node26
  · exact profile88_node27
  · exact profile88_node30

def profile88_node32_cert : CutBound 5 := { lost := (rows 16 0 24 2 10), upper := (rows 15 30 7 29 21), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile88_node32 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,3] 2 profile88_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,3] 2 profile88_node32_cert).mp (by decide +kernel))

def profile88_node34_cert : CutBound 5 := { lost := (rows 16 0 10 20 10), upper := (rows 15 30 21 11 21), lower := (rows 15 30 21 11 16), losses := [{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 28 21 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 11 26 25 11 16) },{ target := 3, region := (rows 1 2 13 0 29), good := (rows 23 22 21 23 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 11 0) }] }

theorem profile88_node34 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,3] 2 profile88_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,3] 2 profile88_node34_cert).mp (by decide +kernel))

def profile88_node35_cert : CutBound 5 := { lost := (rows 16 0 8 18 12), upper := (rows 15 30 21 13 19), lower := (rows 15 30 21 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 29 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 17 25 16) },{ target := 3, region := (rows 1 2 13 0 17), good := (rows 23 22 21 21 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile88_node35 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,5] 2 profile88_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17,5] 2 profile88_node35_cert).mp (by decide +kernel))

def profile88_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node33 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17] 2 (by decide) (choices 2) [3,5] profile88_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28,17] (choices 2) [3,5] profile88_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node34
  · exact profile88_node35

def profile88_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node31 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28] 2 (by decide) (choices 2) [3,17] profile88_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14,28] (choices 2) [3,17] profile88_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node32
  · exact profile88_node33

def profile88_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node1 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile88_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [14] (choices 3) [13,21,25,28] profile88_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile88_node2
  · exact profile88_node8
  · exact profile88_node25
  · exact profile88_node31

def profile88_node38_cert : CutBound 5 := { lost := (rows 0 16 24 2 10), upper := (rows 27 15 7 29 21), lower := (rows 27 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile88_node38 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,3] 2 profile88_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,3] 2 profile88_node38_cert).mp (by decide +kernel))

def profile88_node40_cert : CutBound 5 := { lost := (rows 0 16 10 18 9), upper := (rows 27 15 21 13 22), lower := (rows 27 15 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 30 20 12 16) },{ target := 1, region := (rows 1 0 5 15 16), good := (rows 29 13 29 13 16) },{ target := 3, region := (rows 1 2 15 0 19), good := (rows 23 23 21 21 16) },{ target := 4, region := (rows 1 14 4 14 0), good := (rows 11 15 15 15 0) }] }

theorem profile88_node40 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,5] 2 profile88_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,5] 2 profile88_node40_cert).mp (by decide +kernel))

def profile88_node41_cert : CutBound 5 := { lost := (rows 0 16 10 17 10), upper := (rows 27 15 21 14 21), lower := (rows 27 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 26 14 20 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 21 22 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 14 0) }] }

theorem profile88_node41 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,6] 2 profile88_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17,6] 2 profile88_node41_cert).mp (by decide +kernel))

def profile88_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node39 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17] 2 (by decide) (choices 2) [5,6] profile88_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,17] (choices 2) [5,6] profile88_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node40
  · exact profile88_node41

def profile88_node42_cert : CutBound 5 := { lost := (rows 0 0 9 18 10), upper := (rows 27 15 22 13 21), lower := (rows 27 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 14 8 0) }] }

theorem profile88_node42 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,18] 2 profile88_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13,18] 2 profile88_node42_cert).mp (by decide +kernel))

def profile88_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node37 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13] 2 (by decide) (choices 2) [3,17,18] profile88_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,13] (choices 2) [3,17,18] profile88_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node38
  · exact profile88_node39
  · exact profile88_node42

def profile88_node44_cert : CutBound 5 := { lost := (rows 4 0 24 18 10), upper := (rows 27 30 7 13 21), lower := (rows 27 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 3 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile88_node44 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28,3] 2 profile88_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28,3] 2 profile88_node44_cert).mp (by decide +kernel))

def profile88_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node43 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28] 2 (by decide) (choices 2) [3] profile88_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26,28] (choices 2) [3] profile88_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node44

def profile88_node36_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node36 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26] 2 (by decide) (choices 3) [13,28] profile88_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [26] (choices 3) [13,28] profile88_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node37
  · exact profile88_node43

def profile88_node48_cert : CutBound 5 := { lost := (rows 0 16 24 6 9), upper := (rows 29 15 7 25 22), lower := (rows 29 15 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 28 30 22 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 25 11 11 25 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 17 16) },{ target := 4, region := (rows 1 11 15 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile88_node48 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,17] 2 profile88_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,17] 2 profile88_node48_cert).mp (by decide +kernel))

def profile88_node49_cert : CutBound 5 := { lost := (rows 2 16 24 0 10), upper := (rows 29 15 7 26 21), lower := (rows 29 15 7 26 16), losses := [{ target := 1, region := (rows 3 0 4 8 23), good := (rows 29 29 21 25 16) },{ target := 3, region := (rows 1 2 6 0 23), good := (rows 21 23 23 22 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 14 0) }] }

theorem profile88_node49 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,18] 2 profile88_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,18] 2 profile88_node49_cert).mp (by decide +kernel))

def profile88_node50_cert : CutBound 5 := { lost := (rows 2 0 8 3 12), upper := (rows 29 15 7 28 19), lower := (rows 29 15 7 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 28 14 14 28 16) },{ target := 1, region := (rows 9 0 4 9 16), good := (rows 29 13 13 29 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 25 27 19 24 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 20 16) }] }

theorem profile88_node50 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,20] 2 profile88_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3,20] 2 profile88_node50_cert).mp (by decide +kernel))

def profile88_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node47 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3] 2 (by decide) (choices 2) [17,18,20] profile88_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,3] (choices 2) [17,18,20] profile88_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node48
  · exact profile88_node49
  · exact profile88_node50

def profile88_node52_cert : CutBound 5 := { lost := (rows 0 16 10 20 9), upper := (rows 29 15 21 11 22), lower := (rows 29 15 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 28 30 20 26 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 13 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 11 17 11 16) },{ target := 3, region := (rows 1 2 15 0 26), good := (rows 21 23 21 23 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 11 0) }] }

theorem profile88_node52 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,3] 2 profile88_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,3] 2 profile88_node52_cert).mp (by decide +kernel))

def profile88_node53_cert : CutBound 5 := { lost := (rows 0 16 10 17 12), upper := (rows 29 15 21 14 19), lower := (rows 29 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 28 14 20 14 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 12 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 17 26 16) },{ target := 3, region := (rows 1 2 7 0 18), good := (rows 21 23 21 22 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 14 0) }] }

theorem profile88_node53 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,6] 2 profile88_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17,6] 2 profile88_node53_cert).mp (by decide +kernel))

def profile88_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node51 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17] 2 (by decide) (choices 2) [3,6] profile88_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,17] (choices 2) [3,6] profile88_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node52
  · exact profile88_node53

def profile88_node55_cert : CutBound 5 := { lost := (rows 2 16 8 20 10), upper := (rows 29 15 22 11 21), lower := (rows 29 15 22 11 16), losses := [{ target := 1, region := (rows 3 0 4 8 23), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 11 26 11 16) },{ target := 3, region := (rows 1 2 14 0 27), good := (rows 21 23 22 23 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 11 0) }] }

theorem profile88_node55 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,3] 2 profile88_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,3] 2 profile88_node55_cert).mp (by decide +kernel))

def profile88_node56_cert : CutBound 5 := { lost := (rows 2 16 8 18 12), upper := (rows 29 15 22 13 19), lower := (rows 29 15 22 13 16), losses := [{ target := 1, region := (rows 5 0 4 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 18 9 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 22 5 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile88_node56 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,5] 2 profile88_node56_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18,5] 2 profile88_node56_cert).mp (by decide +kernel))

def profile88_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node54 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18] 2 (by decide) (choices 2) [3,5] profile88_node54_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13,18] (choices 2) [3,5] profile88_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node55
  · exact profile88_node56

def profile88_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node46 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13] 2 (by decide) (choices 2) [3,17,18] profile88_node46_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,13] (choices 2) [3,17,18] profile88_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node47
  · exact profile88_node51
  · exact profile88_node54

def profile88_node59_cert : CutBound 5 := { lost := (rows 0 4 24 18 9), upper := (rows 29 27 7 13 22), lower := (rows 29 27 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 28 26 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 25 13 13 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 3 11 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 21 16) },{ target := 4, region := (rows 1 2 6 15 0), good := (rows 13 15 15 13 0) }] }

theorem profile88_node59 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,5] 2 profile88_node59_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,5] 2 profile88_node59_cert).mp (by decide +kernel))

def profile88_node60_cert : CutBound 5 := { lost := (rows 2 4 8 1 10), upper := (rows 29 27 7 14 21), lower := (rows 29 27 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 28 26 14 14 16) },{ target := 1, region := (rows 9 0 4 8 29), good := (rows 29 25 21 29 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 3 10 16) },{ target := 3, region := (rows 1 2 6 0 23), good := (rows 21 23 23 22 16) }] }

theorem profile88_node60 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,6] 2 profile88_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3,6] 2 profile88_node60_cert).mp (by decide +kernel))

def profile88_node58_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node58 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3] 2 (by decide) (choices 2) [5,6] profile88_node58_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25,3] (choices 2) [5,6] profile88_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node59
  · exact profile88_node60

def profile88_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node57 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25] 2 (by decide) (choices 2) [3] profile88_node57_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,25] (choices 2) [3] profile88_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node58

def profile88_node63_cert : CutBound 5 := { lost := (rows 2 1 8 4 10), upper := (rows 29 30 7 11 21), lower := (rows 29 30 7 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 10 16) },{ target := 1, region := (rows 3 0 4 8 23), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 25 26 11 11 16) },{ target := 3, region := (rows 1 2 12 0 29), good := (rows 21 22 23 23 16) }] }

theorem profile88_node63 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,3] 2 profile88_node63_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,3] 2 profile88_node63_cert).mp (by decide +kernel))

def profile88_node64_cert : CutBound 5 := { lost := (rows 2 1 0 18 12), upper := (rows 29 30 7 13 19), lower := (rows 29 30 7 13 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 14 16) },{ target := 1, region := (rows 3 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 25 26 19 25 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 21 22 23 21 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 13 0) }] }

theorem profile88_node64 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,5] 2 profile88_node64_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3,5] 2 profile88_node64_cert).mp (by decide +kernel))

def profile88_node62_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node62 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3] 2 (by decide) (choices 2) [3,5] profile88_node62_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28,3] (choices 2) [3,5] profile88_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile88_node63
  · exact profile88_node64

def profile88_node61_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node61 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28] 2 (by decide) (choices 2) [3] profile88_node61_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28,28] (choices 2) [3] profile88_node61_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node62

def profile88_node45_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node45 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28] 2 (by decide) (choices 3) [13,25,28] profile88_node45_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [28] (choices 3) [13,25,28] profile88_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node46
  · exact profile88_node57
  · exact profile88_node61

def profile88_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile88_node0 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [] 2 (by decide) (choices 3) [14,26,28] profile88_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [] (choices 3) [14,26,28] profile88_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node1
  · exact profile88_node36
  · exact profile88_node45

theorem profile88 : Upper (D (n:=5) [51,50,35,34,34]) (R (n:=5) [51,50,35,34,34]) [] 2 := profile88_node0

def profile89_node2_cert : CutBound 5 := { lost := (rows 16 16 8 0 8), upper := (rows 15 15 21 29 21), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node2 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,13] 2 profile89_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,13] 2 profile89_node2_cert).mp (by decide +kernel))

def profile89_node4_cert : CutBound 5 := { lost := (rows 0 8 16 0 8), upper := (rows 15 23 13 29 21), lower := (rows 15 23 13 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile89_node4 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,9] 2 profile89_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,9] 2 profile89_node4_cert).mp (by decide +kernel))

def profile89_node5_cert : CutBound 5 := { lost := (rows 16 8 8 16 0), upper := (rows 15 23 21 13 29), lower := (rows 15 23 21 8 16), losses := [{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 8 0) }] }

theorem profile89_node5 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,17] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,17] 2 profile89_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,17] 2 profile89_node5_cert).mp (by decide +kernel))

def profile89_node6_cert : CutBound 5 := { lost := (rows 16 8 0 16 8), upper := (rows 15 23 28 13 21), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile89_node6 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,24] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,24] 2 profile89_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21,24] 2 profile89_node6_cert).mp (by decide +kernel))

def profile89_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node3 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21] 2 (by decide) (choices 2) [9,17,24] profile89_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,21] (choices 2) [9,17,24] profile89_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node4
  · exact profile89_node5
  · exact profile89_node6

def profile89_node7_cert : CutBound 5 := { lost := (rows 16 0 8 0 8), upper := (rows 15 30 21 29 21), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node7 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,28] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,28] 2 profile89_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14,28] 2 profile89_node7_cert).mp (by decide +kernel))

def profile89_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node1 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile89_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [14] (choices 3) [13,21,28] profile89_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node2
  · exact profile89_node3
  · exact profile89_node7

def profile89_node9_cert : CutBound 5 := { lost := (rows 0 16 8 0 8), upper := (rows 29 15 23 31 23), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node9 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,13] 2 profile89_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,13] 2 profile89_node9_cert).mp (by decide +kernel))

def profile89_node11_cert : CutBound 5 := { lost := (rows 0 1 0 16 8), upper := (rows 29 30 7 13 21), lower := (rows 29 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 21 22 23 0 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 8 0) }] }

theorem profile89_node11 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28,3] 2 profile89_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28,3] 2 profile89_node11_cert).mp (by decide +kernel))

def profile89_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node10 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28] 2 (by decide) (choices 2) [3] profile89_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28,28] (choices 2) [3] profile89_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node11

def profile89_node8_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node8 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28] 2 (by decide) (choices 3) [13,28] profile89_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [28] (choices 3) [13,28] profile89_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node9
  · exact profile89_node10

def profile89_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile89_node0 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [] 2 (by decide) (choices 3) [14,28] profile89_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [] (choices 3) [14,28] profile89_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile89_node1
  · exact profile89_node8

theorem profile89 : Upper (D (n:=5) [51,49,36,34,34]) (R (n:=5) [51,49,36,34,34]) [] 2 := profile89_node0

def profile90_node3_cert : CutBound 5 := { lost := (rows 16 16 8 1 9), upper := (rows 15 15 21 30 22), lower := (rows 15 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile90_node3 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,17] 2 profile90_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,17] 2 profile90_node3_cert).mp (by decide +kernel))

def profile90_node4_cert : CutBound 5 := { lost := (rows 16 16 8 2 10), upper := (rows 15 15 22 29 21), lower := (rows 15 15 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile90_node4 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,18] 2 profile90_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13,18] 2 profile90_node4_cert).mp (by decide +kernel))

def profile90_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node2 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13] 2 (by decide) (choices 2) [17,18] profile90_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,13] (choices 2) [17,18] profile90_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node3
  · exact profile90_node4

def profile90_node6_cert : CutBound 5 := { lost := (rows 0 0 24 3 3), upper := (rows 15 23 7 28 28), lower := (rows 15 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile90_node6 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,3] 2 profile90_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,3] 2 profile90_node6_cert).mp (by decide +kernel))

def profile90_node7_cert : CutBound 5 := { lost := (rows 0 8 18 1 9), upper := (rows 15 23 13 30 22), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile90_node7 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,9] 2 profile90_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,9] 2 profile90_node7_cert).mp (by decide +kernel))

def profile90_node8_cert : CutBound 5 := { lost := (rows 16 8 17 2 10), upper := (rows 15 23 14 29 21), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile90_node8 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,10] 2 profile90_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,10] 2 profile90_node8_cert).mp (by decide +kernel))

def profile90_node9_cert : CutBound 5 := { lost := (rows 16 8 10 17 1), upper := (rows 15 23 21 14 30), lower := (rows 15 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile90_node9 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,17] 2 profile90_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,17] 2 profile90_node9_cert).mp (by decide +kernel))

def profile90_node10_cert : CutBound 5 := { lost := (rows 16 0 9 18 2), upper := (rows 15 23 22 13 29), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile90_node10 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,18] 2 profile90_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,18] 2 profile90_node10_cert).mp (by decide +kernel))

def profile90_node12_cert : CutBound 5 := { lost := (rows 0 8 3 2 9), upper := (rows 15 23 28 13 22), lower := (rows 15 23 28 13 16), losses := [{ target := 0, region := (rows 0 2 13 8 19), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) },{ target := 3, region := (rows 1 11 4 0 31), good := (rows 23 23 22 23 16) }] }

theorem profile90_node12 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,5] 2 profile90_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,5] 2 profile90_node12_cert).mp (by decide +kernel))

def profile90_node13_cert : CutBound 5 := { lost := (rows 0 8 3 1 10), upper := (rows 15 23 28 14 21), lower := (rows 15 23 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) },{ target := 1, region := (rows 1 0 13 8 19), good := (rows 29 21 28 28 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 22 16) }] }

theorem profile90_node13 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,6] 2 profile90_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24,6] 2 profile90_node13_cert).mp (by decide +kernel))

def profile90_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node11 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24] 2 (by decide) (choices 2) [5,6] profile90_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21,24] (choices 2) [5,6] profile90_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node12
  · exact profile90_node13

def profile90_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node5 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile90_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,21] (choices 2) [3,9,10,17,18,24] profile90_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile90_node6
  · exact profile90_node7
  · exact profile90_node8
  · exact profile90_node9
  · exact profile90_node10
  · exact profile90_node11

def profile90_node15_cert : CutBound 5 := { lost := (rows 16 0 24 2 10), upper := (rows 15 30 7 29 21), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile90_node15 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,3] 2 profile90_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,3] 2 profile90_node15_cert).mp (by decide +kernel))

def profile90_node17_cert : CutBound 5 := { lost := (rows 16 1 8 18 9), upper := (rows 15 30 21 13 22), lower := (rows 15 30 21 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 31), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 29 13 16) },{ target := 3, region := (rows 1 2 13 0 19), good := (rows 23 22 21 21 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile90_node17 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,5] 2 profile90_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,5] 2 profile90_node17_cert).mp (by decide +kernel))

def profile90_node18_cert : CutBound 5 := { lost := (rows 0 1 10 1 10), upper := (rows 15 30 21 14 21), lower := (rows 15 30 21 14 16), losses := [{ target := 0, region := (rows 0 6 4 15 16), good := (rows 14 30 30 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 21 28 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 21 22 16) }] }

theorem profile90_node18 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,6] 2 profile90_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17,6] 2 profile90_node18_cert).mp (by decide +kernel))

def profile90_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node16 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17] 2 (by decide) (choices 2) [5,6] profile90_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,17] (choices 2) [5,6] profile90_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node17
  · exact profile90_node18

def profile90_node19_cert : CutBound 5 := { lost := (rows 16 0 9 18 10), upper := (rows 15 30 22 13 21), lower := (rows 15 30 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 20 8 16) },{ target := 3, region := (rows 1 2 7 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile90_node19 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,18] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,18] 2 profile90_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28,18] 2 profile90_node19_cert).mp (by decide +kernel))

def profile90_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node14 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28] 2 (by decide) (choices 2) [3,17,18] profile90_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14,28] (choices 2) [3,17,18] profile90_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node15
  · exact profile90_node16
  · exact profile90_node19

def profile90_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node1 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile90_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [14] (choices 3) [13,21,28] profile90_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node2
  · exact profile90_node5
  · exact profile90_node14

def profile90_node22_cert : CutBound 5 := { lost := (rows 0 16 24 1 9), upper := (rows 29 15 7 30 22), lower := (rows 29 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile90_node22 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,3] 2 profile90_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,3] 2 profile90_node22_cert).mp (by decide +kernel))

def profile90_node23_cert : CutBound 5 := { lost := (rows 0 16 10 17 9), upper := (rows 29 15 21 14 22), lower := (rows 29 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 7 0 18), good := (rows 21 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile90_node23 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,17] 2 profile90_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,17] 2 profile90_node23_cert).mp (by decide +kernel))

def profile90_node25_cert : CutBound 5 := { lost := (rows 2 0 9 2 9), upper := (rows 29 15 22 13 22), lower := (rows 29 15 22 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 28 30 22 28 16) },{ target := 1, region := (rows 5 0 4 15 16), good := (rows 29 13 29 13 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 22 21 16) }] }

theorem profile90_node25 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,5] 2 profile90_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,5] 2 profile90_node25_cert).mp (by decide +kernel))

def profile90_node26_cert : CutBound 5 := { lost := (rows 2 16 8 17 10), upper := (rows 29 15 22 14 21), lower := (rows 29 15 22 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 28 14 30 14 16) },{ target := 1, region := (rows 11 0 4 8 31), good := (rows 29 29 21 29 16) },{ target := 3, region := (rows 1 2 14 0 19), good := (rows 21 23 22 22 16) },{ target := 4, region := (rows 1 3 4 15 0), good := (rows 15 15 14 14 0) }] }

theorem profile90_node26 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,6] 2 profile90_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18,6] 2 profile90_node26_cert).mp (by decide +kernel))

def profile90_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node24 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18] 2 (by decide) (choices 2) [5,6] profile90_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13,18] (choices 2) [5,6] profile90_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node25
  · exact profile90_node26

def profile90_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node21 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13] 2 (by decide) (choices 2) [3,17,18] profile90_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,13] (choices 2) [3,17,18] profile90_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node22
  · exact profile90_node23
  · exact profile90_node24

def profile90_node29_cert : CutBound 5 := { lost := (rows 2 1 0 18 9), upper := (rows 29 30 7 13 22), lower := (rows 29 30 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 31), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 3 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 3, region := (rows 1 2 4 0 22), good := (rows 21 22 23 21 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 13 0) }] }

theorem profile90_node29 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,5] 2 profile90_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,5] 2 profile90_node29_cert).mp (by decide +kernel))

def profile90_node30_cert : CutBound 5 := { lost := (rows 2 1 0 17 10), upper := (rows 29 30 7 14 21), lower := (rows 29 30 7 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 11 0 4 8 31), good := (rows 29 29 21 29 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 21 22 23 22 16) },{ target := 4, region := (rows 1 2 4 14 0), good := (rows 13 14 15 14 0) }] }

theorem profile90_node30 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,6] 2 profile90_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3,6] 2 profile90_node30_cert).mp (by decide +kernel))

def profile90_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node28 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3] 2 (by decide) (choices 2) [5,6] profile90_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28,3] (choices 2) [5,6] profile90_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node29
  · exact profile90_node30

def profile90_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node27 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28] 2 (by decide) (choices 2) [3] profile90_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28,28] (choices 2) [3] profile90_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile90_node28

def profile90_node20_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile90_node20 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28] 2 (by decide) (choices 3) [13,28] profile90_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [28] (choices 3) [13,28] profile90_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node21
  · exact profile90_node27

def profile90_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile90_node0 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [] 2 (by decide) (choices 3) [14,28] profile90_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [] (choices 3) [14,28] profile90_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node1
  · exact profile90_node20

theorem profile90 : Upper (D (n:=5) [50,50,36,34,34]) (R (n:=5) [50,50,36,34,34]) [] 2 := profile90_node0

def profile91_node3_cert : CutBound 5 := { lost := (rows 0 24 16 0 0), upper := (rows 31 7 14 30 30), lower := (rows 31 7 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 6 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile91_node3 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,10] 2 profile91_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,10] 2 profile91_node3_cert).mp (by decide +kernel))

def profile91_node4_cert : CutBound 5 := { lost := (rows 0 24 2 16 0), upper := (rows 31 7 28 14 30), lower := (rows 31 7 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 28 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile91_node4 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,24] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,24] 2 profile91_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5,24] 2 profile91_node4_cert).mp (by decide +kernel))

def profile91_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node2 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5] 2 (by decide) (choices 2) [10,24] profile91_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,5] (choices 2) [10,24] profile91_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node3
  · exact profile91_node4

def profile91_node6_cert : CutBound 5 := { lost := (rows 0 16 24 0 0), upper := (rows 31 14 7 30 30), lower := (rows 31 14 7 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile91_node6 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,3] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,3] 2 profile91_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,3] 2 profile91_node6_cert).mp (by decide +kernel))

def profile91_node7_cert : CutBound 5 := { lost := (rows 0 16 18 0 8), upper := (rows 31 14 13 30 22), lower := (rows 31 14 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 1 7 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile91_node7 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,9] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,9] 2 profile91_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,9] 2 profile91_node7_cert).mp (by decide +kernel))

def profile91_node8_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 31 14 14 31 23), lower := (rows 31 14 14 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 6 6 0 16) },{ target := 4, region := (rows 1 15 15 8 0), good := (rows 15 14 14 14 0) }] }

theorem profile91_node8 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,10] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,10] 2 profile91_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,10] 2 profile91_node8_cert).mp (by decide +kernel))

def profile91_node9_cert : CutBound 5 := { lost := (rows 0 16 10 16 0), upper := (rows 31 14 21 14 30), lower := (rows 31 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 14 15 8 0) }] }

theorem profile91_node9 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,17] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,17] 2 profile91_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,17] 2 profile91_node9_cert).mp (by decide +kernel))

def profile91_node10_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 31 14 22 15 31), lower := (rows 31 14 22 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 22 0 16) },{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 14 6 8 0) }] }

theorem profile91_node10 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,18] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,18] 2 profile91_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,18] 2 profile91_node10_cert).mp (by decide +kernel))

def profile91_node11_cert : CutBound 5 := { lost := (rows 0 16 2 16 8), upper := (rows 31 14 28 15 23), lower := (rows 31 14 28 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 28 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 6 20 0 16) },{ target := 4, region := (rows 1 7 4 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile91_node11 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,24] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,24] 2 profile91_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12,24] 2 profile91_node11_cert).mp (by decide +kernel))

def profile91_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node5 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12] 2 := by
  apply routed_branch (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile91_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,12] (choices 2) [3,9,10,17,18,24] profile91_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile91_node6
  · exact profile91_node7
  · exact profile91_node8
  · exact profile91_node9
  · exact profile91_node10
  · exact profile91_node11

def profile91_node12_cert : CutBound 5 := { lost := (rows 0 12 16 16 0), upper := (rows 31 19 14 14 30), lower := (rows 31 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 19 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile91_node12 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,17] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,17] 2 profile91_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,17] 2 profile91_node12_cert).mp (by decide +kernel))

def profile91_node13_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 22 15 15 31), lower := (rows 31 22 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile91_node13 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,20] 2 :=
  cut_bound_sound (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,20] 2 profile91_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30,20] 2 profile91_node13_cert).mp (by decide +kernel))

def profile91_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile91_node1 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30] 2 (by decide) (choices 2) [5,12,17,20] profile91_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [30] (choices 2) [5,12,17,20] profile91_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile91_node2
  · exact profile91_node5
  · exact profile91_node12
  · exact profile91_node13

def profile91_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node0 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [] 2 (by decide) (choices 4) [30] profile91_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [] (choices 4) [30] profile91_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node1

theorem profile91 : Upper (D (n:=5) [65,35,35,35,34]) (R (n:=5) [65,35,35,35,34]) [] 2 := profile91_node0

def profile92_node4_cert : CutBound 5 := { lost := (rows 0 0 8 4 1), upper := (rows 15 15 21 25 28), lower := (rows 15 15 21 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 24 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 25 25 16) },{ target := 3, region := (rows 1 2 12 0 16), good := (rows 7 7 21 21 16) }] }

theorem profile92_node4 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,17] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,17] 2 profile92_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,17] 2 profile92_node4_cert).mp (by decide +kernel))

def profile92_node5_cert : CutBound 5 := { lost := (rows 16 16 0 1 4), upper := (rows 15 15 21 28 25), lower := (rows 15 15 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 28 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 24 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile92_node5 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,20] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,20] 2 profile92_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17,20] 2 profile92_node5_cert).mp (by decide +kernel))

def profile92_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node3 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17] 2 (by decide) (choices 2) [17,20] profile92_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,17] (choices 2) [17,20] profile92_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node4
  · exact profile92_node5

def profile92_node6_cert : CutBound 5 := { lost := (rows 16 16 0 0 8), upper := (rows 15 15 28 29 21), lower := (rows 15 15 28 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile92_node6 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,24] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,24] 2 profile92_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13,24] 2 profile92_node6_cert).mp (by decide +kernel))

def profile92_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node2 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13] 2 (by decide) (choices 2) [17,24] profile92_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,13] (choices 2) [17,24] profile92_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node3
  · exact profile92_node6

def profile92_node9_cert : CutBound 5 := { lost := (rows 0 0 16 4 1), upper := (rows 15 23 13 25 28), lower := (rows 15 23 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 28 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 25 16) },{ target := 4, region := (rows 1 2 13 8 0), good := (rows 15 7 13 13 0) }] }

theorem profile92_node9 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,17] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,17] 2 profile92_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,17] 2 profile92_node9_cert).mp (by decide +kernel))

def profile92_node10_cert : CutBound 5 := { lost := (rows 0 0 16 1 4), upper := (rows 15 23 13 28 25), lower := (rows 15 23 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 12 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 25 24 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 12 0) }] }

theorem profile92_node10 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,20] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,20] 2 profile92_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9,20] 2 profile92_node10_cert).mp (by decide +kernel))

def profile92_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node8 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9] 2 (by decide) (choices 2) [17,20] profile92_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,9] (choices 2) [17,20] profile92_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node9
  · exact profile92_node10

def profile92_node12_cert : CutBound 5 := { lost := (rows 16 0 0 16 4), upper := (rows 15 23 28 13 25), lower := (rows 15 23 28 13 16), losses := [{ target := 2, region := (rows 1 2 0 8 25), good := (rows 27 19 24 25 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 13 0) }] }

theorem profile92_node12 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24,5] 2 profile92_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24,5] 2 profile92_node12_cert).mp (by decide +kernel))

def profile92_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node11 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24] 2 (by decide) (choices 2) [5] profile92_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21,24] (choices 2) [5] profile92_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node12

def profile92_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node7 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21] 2 (by decide) (choices 2) [9,24] profile92_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,21] (choices 2) [9,24] profile92_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node8
  · exact profile92_node11

def profile92_node14_cert : CutBound 5 := { lost := (rows 16 0 16 0 8), upper := (rows 15 30 13 29 21), lower := (rows 15 30 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 13 8 0) }] }

theorem profile92_node14 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,9] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,9] 2 profile92_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,9] 2 profile92_node14_cert).mp (by decide +kernel))

def profile92_node16_cert : CutBound 5 := { lost := (rows 16 0 0 16 4), upper := (rows 15 30 21 13 25), lower := (rows 15 30 21 13 16), losses := [{ target := 2, region := (rows 1 2 0 8 25), good := (rows 27 26 17 25 16) },{ target := 4, region := (rows 3 2 4 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile92_node16 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17,5] 2 profile92_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17,5] 2 profile92_node16_cert).mp (by decide +kernel))

def profile92_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node15 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17] 2 (by decide) (choices 2) [5] profile92_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28,17] (choices 2) [5] profile92_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node16

def profile92_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node13 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28] 2 (by decide) (choices 2) [9,17] profile92_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14,28] (choices 2) [9,17] profile92_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node14
  · exact profile92_node15

def profile92_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile92_node1 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile92_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [14] (choices 3) [13,21,28] profile92_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node2
  · exact profile92_node7
  · exact profile92_node13

def profile92_node20_cert : CutBound 5 := { lost := (rows 0 16 16 4 1), upper := (rows 23 15 13 25 28), lower := (rows 23 15 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 28 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 9 25 16) },{ target := 4, region := (rows 1 14 14 8 0), good := (rows 7 15 15 15 0) }] }

theorem profile92_node20 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,17] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,17] 2 profile92_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,17] 2 profile92_node20_cert).mp (by decide +kernel))

def profile92_node21_cert : CutBound 5 := { lost := (rows 0 16 16 1 4), upper := (rows 23 15 13 28 25), lower := (rows 23 15 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 12 28 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 19 27 25 24 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 14 0) }] }

theorem profile92_node21 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,20] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,20] 2 profile92_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9,20] 2 profile92_node21_cert).mp (by decide +kernel))

def profile92_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node19 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9] 2 (by decide) (choices 2) [17,20] profile92_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,9] (choices 2) [17,20] profile92_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node20
  · exact profile92_node21

def profile92_node23_cert : CutBound 5 := { lost := (rows 0 16 0 16 4), upper := (rows 23 15 28 13 25), lower := (rows 23 15 28 13 16), losses := [{ target := 2, region := (rows 1 2 0 8 26), good := (rows 19 27 24 25 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile92_node23 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24,5] 2 profile92_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24,5] 2 profile92_node23_cert).mp (by decide +kernel))

def profile92_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node22 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24] 2 (by decide) (choices 2) [5] profile92_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13,24] (choices 2) [5] profile92_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node23

def profile92_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node18 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13] 2 (by decide) (choices 2) [9,24] profile92_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,13] (choices 2) [9,24] profile92_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node19
  · exact profile92_node22

def profile92_node26_cert : CutBound 5 := { lost := (rows 0 0 16 16 1), upper := (rows 23 27 13 13 28), lower := (rows 23 27 13 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 28), good := (rows 22 26 28 28 16) },{ target := 4, region := (rows 1 2 15 15 0), good := (rows 15 15 13 13 0) }] }

theorem profile92_node26 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9,5] 2 profile92_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9,5] 2 profile92_node26_cert).mp (by decide +kernel))

def profile92_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node25 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9] 2 (by decide) (choices 2) [5] profile92_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25,9] (choices 2) [5] profile92_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node26

def profile92_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node24 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25] 2 (by decide) (choices 2) [9] profile92_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,25] (choices 2) [9] profile92_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node25

def profile92_node27_cert : CutBound 5 := { lost := (rows 8 0 16 16 0), upper := (rows 23 30 13 13 29), lower := (rows 23 30 4 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile92_node27 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,28] 2 profile92_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22,28] 2 profile92_node27_cert).mp (by decide +kernel))

def profile92_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node17 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22] 2 (by decide) (choices 3) [13,25,28] profile92_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [22] (choices 3) [13,25,28] profile92_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node18
  · exact profile92_node24
  · exact profile92_node27

def profile92_node30_cert : CutBound 5 := { lost := (rows 0 16 24 0 0), upper := (rows 29 15 7 29 29), lower := (rows 29 15 7 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 7 7 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile92_node30 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,3] 2 profile92_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,3] 2 profile92_node30_cert).mp (by decide +kernel))

def profile92_node31_cert : CutBound 5 := { lost := (rows 0 16 16 0 8), upper := (rows 29 15 13 31 23), lower := (rows 29 15 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 5 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile92_node31 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,9] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,9] 2 profile92_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,9] 2 profile92_node31_cert).mp (by decide +kernel))

def profile92_node32_cert : CutBound 5 := { lost := (rows 0 16 17 0 8), upper := (rows 29 15 14 29 21), lower := (rows 29 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 14 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 21 23 22 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile92_node32 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,10] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,10] 2 profile92_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,10] 2 profile92_node32_cert).mp (by decide +kernel))

def profile92_node33_cert : CutBound 5 := { lost := (rows 0 16 8 16 0), upper := (rows 29 15 21 15 31), lower := (rows 29 15 21 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 21 7 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile92_node33 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,17] 2 profile92_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,17] 2 profile92_node33_cert).mp (by decide +kernel))

def profile92_node35_cert : CutBound 5 := { lost := (rows 0 16 0 16 4), upper := (rows 29 15 22 13 25), lower := (rows 29 15 22 13 16), losses := [{ target := 2, region := (rows 1 2 0 8 27), good := (rows 25 27 18 25 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile92_node35 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18,5] 2 profile92_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18,5] 2 profile92_node35_cert).mp (by decide +kernel))

def profile92_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node34 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18] 2 (by decide) (choices 2) [5] profile92_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,18] (choices 2) [5] profile92_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node35

def profile92_node36_cert : CutBound 5 := { lost := (rows 0 16 1 16 8), upper := (rows 29 15 28 15 23), lower := (rows 29 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 28 14 28 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 21 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile92_node36 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,24] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,24] 2 profile92_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13,24] 2 profile92_node36_cert).mp (by decide +kernel))

def profile92_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node29 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile92_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,13] (choices 2) [3,9,10,17,18,24] profile92_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile92_node30
  · exact profile92_node31
  · exact profile92_node32
  · exact profile92_node33
  · exact profile92_node34
  · exact profile92_node36

def profile92_node37_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 29 23 15 15 31), lower := (rows 29 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile92_node37 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,21] 2 profile92_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,21] 2 profile92_node37_cert).mp (by decide +kernel))

def profile92_node40_cert : CutBound 5 := { lost := (rows 0 1 0 16 4), upper := (rows 29 30 7 13 25), lower := (rows 29 30 7 13 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 14 16) },{ target := 2, region := (rows 1 2 0 8 25), good := (rows 25 26 19 25 16) },{ target := 4, region := (rows 1 2 4 13 0), good := (rows 13 14 15 13 0) }] }

theorem profile92_node40 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3,5] 2 profile92_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3,5] 2 profile92_node40_cert).mp (by decide +kernel))

def profile92_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node39 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3] 2 (by decide) (choices 2) [5] profile92_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,3] (choices 2) [5] profile92_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node40

def profile92_node42_cert : CutBound 5 := { lost := (rows 0 1 16 0 8), upper := (rows 29 30 13 11 21), lower := (rows 29 30 13 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 10 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 21 22 21 19 16) },{ target := 4, region := (rows 1 2 13 8 0), good := (rows 13 14 13 15 0) }] }

theorem profile92_node42 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,3] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,3] 2 profile92_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,3] 2 profile92_node42_cert).mp (by decide +kernel))

def profile92_node43_cert : CutBound 5 := { lost := (rows 0 1 16 16 0), upper := (rows 29 30 13 13 19), lower := (rows 29 30 13 13 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 14 16) },{ target := 4, region := (rows 1 2 13 13 0), good := (rows 13 14 13 13 0) }] }

theorem profile92_node43 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,5] 2 :=
  cut_bound_sound (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,5] 2 profile92_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9,5] 2 profile92_node43_cert).mp (by decide +kernel))

def profile92_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node41 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9] 2 (by decide) (choices 2) [3,5] profile92_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28,9] (choices 2) [3,5] profile92_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node42
  · exact profile92_node43

def profile92_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node38 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28] 2 (by decide) (choices 2) [3,9] profile92_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28,28] (choices 2) [3,9] profile92_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node39
  · exact profile92_node41

def profile92_node28_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile92_node28 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28] 2 (by decide) (choices 3) [13,21,28] profile92_node28_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [28] (choices 3) [13,21,28] profile92_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node29
  · exact profile92_node37
  · exact profile92_node38

def profile92_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile92_node0 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [] 2 (by decide) (choices 3) [14,22,28] profile92_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [] (choices 3) [14,22,28] profile92_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node1
  · exact profile92_node17
  · exact profile92_node28

theorem profile92 : Upper (D (n:=5) [51,49,35,35,34]) (R (n:=5) [51,49,35,35,34]) [] 2 := profile92_node0

#print axioms profile92
end Delivery.FiveVertexPositive12
