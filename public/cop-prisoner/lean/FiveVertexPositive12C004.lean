import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile67_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile67_node2 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,21] 2 profile67_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,21] 2 profile67_node2_cert).mp (by decide +kernel))

def profile67_node4_cert : CutBound 5 := { lost := (rows 8 0 8 3 0), upper := (rows 23 27 23 28 28), lower := (rows 23 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile67_node4 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,19] 2 profile67_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,19] 2 profile67_node4_cert).mp (by decide +kernel))

def profile67_node5_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 23 27 29 30 22), lower := (rows 23 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) }] }

theorem profile67_node5 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,25] 2 profile67_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,25] 2 profile67_node5_cert).mp (by decide +kernel))

def profile67_node6_cert : CutBound 5 := { lost := (rows 8 0 1 2 0), upper := (rows 23 27 30 29 21), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile67_node6 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,26] 2 profile67_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25,26] 2 profile67_node6_cert).mp (by decide +kernel))

def profile67_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node3 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25] 2 (by decide) (choices 3) [19,25,26] profile67_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,25] (choices 3) [19,25,26] profile67_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node4
  · exact profile67_node5
  · exact profile67_node6

def profile67_node8_cert : CutBound 5 := { lost := (rows 8 0 8 6 0), upper := (rows 23 30 23 25 25), lower := (rows 23 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile67_node8 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,19] 2 profile67_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,19] 2 profile67_node8_cert).mp (by decide +kernel))

def profile67_node9_cert : CutBound 5 := { lost := (rows 8 1 0 4 0), upper := (rows 23 30 29 27 19), lower := (rows 23 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile67_node9 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,25] 2 profile67_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,25] 2 profile67_node9_cert).mp (by decide +kernel))

def profile67_node10_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 23 30 30 25 17), lower := (rows 23 30 30 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 22 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) }] }

theorem profile67_node10 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,26] 2 profile67_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28,26] 2 profile67_node10_cert).mp (by decide +kernel))

def profile67_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node7 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28] 2 (by decide) (choices 3) [19,25,26] profile67_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22,28] (choices 3) [19,25,26] profile67_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node8
  · exact profile67_node9
  · exact profile67_node10

def profile67_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node1 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22] 2 (by decide) (choices 3) [21,25,28] profile67_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [22] (choices 3) [21,25,28] profile67_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node2
  · exact profile67_node3
  · exact profile67_node7

def profile67_node13_cert : CutBound 5 := { lost := (rows 0 8 8 3 0), upper := (rows 27 23 23 28 28), lower := (rows 27 23 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile67_node13 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,19] 2 profile67_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,19] 2 profile67_node13_cert).mp (by decide +kernel))

def profile67_node14_cert : CutBound 5 := { lost := (rows 0 8 2 1 0), upper := (rows 27 23 29 30 22), lower := (rows 27 23 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) }] }

theorem profile67_node14 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,25] 2 profile67_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,25] 2 profile67_node14_cert).mp (by decide +kernel))

def profile67_node15_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 23 30 29 21), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 19 27 8 16) }] }

theorem profile67_node15 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,26] 2 profile67_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21,26] 2 profile67_node15_cert).mp (by decide +kernel))

def profile67_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node12 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21] 2 (by decide) (choices 3) [19,25,26] profile67_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,21] (choices 3) [19,25,26] profile67_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node13
  · exact profile67_node14
  · exact profile67_node15

def profile67_node16_cert : CutBound 5 := { lost := (rows 4 4 8 0 0), upper := (rows 27 27 23 31 23), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile67_node16 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,25] 2 profile67_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,25] 2 profile67_node16_cert).mp (by decide +kernel))

def profile67_node18_cert : CutBound 5 := { lost := (rows 4 0 8 2 0), upper := (rows 27 30 23 29 21), lower := (rows 27 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 25 28 29 8 16) },{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 19 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile67_node18 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28,19] 2 profile67_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28,19] 2 profile67_node18_cert).mp (by decide +kernel))

def profile67_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node17 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28] 2 (by decide) (choices 3) [19] profile67_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26,28] (choices 3) [19] profile67_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node18

def profile67_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node11 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26] 2 (by decide) (choices 3) [21,25,28] profile67_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [26] (choices 3) [21,25,28] profile67_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile67_node12
  · exact profile67_node16
  · exact profile67_node17

def profile67_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile67_node0 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [] 2 (by decide) (choices 3) [22,26] profile67_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [] (choices 3) [22,26] profile67_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node1
  · exact profile67_node11

theorem profile67 : Upper (D (n:=5) [50,50,50,34,20]) (R (n:=5) [50,50,50,34,20]) [] 2 := profile67_node0

def profile68_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 29 26 26), lower := (rows 23 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 26 28 8 16) }] }

theorem profile68_node3 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,25] 2 profile68_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,25] 2 profile68_node3_cert).mp (by decide +kernel))

def profile68_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 27 30 25 25), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) }] }

theorem profile68_node4 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,26] 2 profile68_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25,26] 2 profile68_node4_cert).mp (by decide +kernel))

def profile68_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node2 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25] 2 (by decide) (choices 3) [25,26] profile68_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22,25] (choices 3) [25,26] profile68_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node3
  · exact profile68_node4

def profile68_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node1 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22] 2 (by decide) (choices 3) [25] profile68_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [22] (choices 3) [25] profile68_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node2

def profile68_node7_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 29 26 26), lower := (rows 27 23 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 26 30 28 8 16) }] }

theorem profile68_node7 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,25] 2 profile68_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,25] 2 profile68_node7_cert).mp (by decide +kernel))

def profile68_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 23 30 25 25), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) }] }

theorem profile68_node8 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,26] 2 profile68_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21,26] 2 profile68_node8_cert).mp (by decide +kernel))

def profile68_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node6 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21] 2 (by decide) (choices 3) [25,26] profile68_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,21] (choices 3) [25,26] profile68_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile68_node7
  · exact profile68_node8

def profile68_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 27 23 28 28), lower := (rows 27 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 12 20), good := (rows 26 26 30 8 16) }] }

theorem profile68_node10 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,19] 2 profile68_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,19] 2 profile68_node10_cert).mp (by decide +kernel))

def profile68_node11_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 27 29 30 22), lower := (rows 27 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile68_node11 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,25] 2 profile68_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,25] 2 profile68_node11_cert).mp (by decide +kernel))

def profile68_node12_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 27 30 29 21), lower := (rows 27 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile68_node12 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,26] 2 profile68_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25,26] 2 profile68_node12_cert).mp (by decide +kernel))

def profile68_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node9 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25] 2 (by decide) (choices 3) [19,25,26] profile68_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,25] (choices 3) [19,25,26] profile68_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node10
  · exact profile68_node11
  · exact profile68_node12

def profile68_node14_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 30 23 25 25), lower := (rows 27 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 25 28 29 8 16) }] }

theorem profile68_node14 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,19] 2 profile68_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,19] 2 profile68_node14_cert).mp (by decide +kernel))

def profile68_node15_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 27 30 29 27 19), lower := (rows 27 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 26 30 30 8 16) }] }

theorem profile68_node15 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,25] 2 profile68_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,25] 2 profile68_node15_cert).mp (by decide +kernel))

def profile68_node16_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 27 30 30 25 17), lower := (rows 27 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile68_node16 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,26] 2 profile68_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28,26] 2 profile68_node16_cert).mp (by decide +kernel))

def profile68_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node13 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28] 2 (by decide) (choices 3) [19,25,26] profile68_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26,28] (choices 3) [19,25,26] profile68_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node14
  · exact profile68_node15
  · exact profile68_node16

def profile68_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node5 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26] 2 (by decide) (choices 3) [21,25,28] profile68_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [26] (choices 3) [21,25,28] profile68_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node6
  · exact profile68_node9
  · exact profile68_node13

def profile68_node19_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 27 23 26 26), lower := (rows 29 27 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 26 30 8 16) }] }

theorem profile68_node19 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,19] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,19] 2 profile68_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,19] 2 profile68_node19_cert).mp (by decide +kernel))

def profile68_node20_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 29 27 29 26 18), lower := (rows 29 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 26 28 8 16) }] }

theorem profile68_node20 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,25] 2 profile68_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,25] 2 profile68_node20_cert).mp (by decide +kernel))

def profile68_node21_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 29 27 30 27 19), lower := (rows 29 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 30 30 8 16) }] }

theorem profile68_node21 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,26] 2 profile68_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25,26] 2 profile68_node21_cert).mp (by decide +kernel))

def profile68_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node18 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25] 2 (by decide) (choices 3) [19,25,26] profile68_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28,25] (choices 3) [19,25,26] profile68_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node19
  · exact profile68_node20
  · exact profile68_node21

def profile68_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node17 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28] 2 (by decide) (choices 3) [25] profile68_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [28] (choices 3) [25] profile68_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node18

def profile68_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node0 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [] 2 (by decide) (choices 3) [22,26,28] profile68_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [] (choices 3) [22,26,28] profile68_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node1
  · exact profile68_node5
  · exact profile68_node17

theorem profile68 : Upper (D (n:=5) [50,50,49,35,20]) (R (n:=5) [50,50,49,35,20]) [] 2 := profile68_node0

def profile69_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 31 7 15 11 27), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile69_node2 : Upper (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30,5] 2 :=
  cut_bound_sound (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30,5] 2 profile69_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30,5] 2 profile69_node2_cert).mp (by decide +kernel))

def profile69_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile69_node1 : Upper (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30] 2 (by decide) (choices 2) [5] profile69_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [30] (choices 2) [5] profile69_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node2

def profile69_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node0 : Upper (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [] 2 (by decide) (choices 4) [30] profile69_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [] (choices 4) [30] profile69_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node1

theorem profile69 : Upper (D (n:=5) [68,35,34,34,33]) (R (n:=5) [68,35,34,34,33]) [] 2 := profile69_node0

def profile70_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 31 7 15 11 27), lower := (rows 31 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile70_node2 : Upper (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,5] 2 :=
  cut_bound_sound (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,5] 2 profile70_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,5] 2 profile70_node2_cert).mp (by decide +kernel))

def profile70_node3_cert : CutBound 5 := { lost := (rows 0 1 0 4 4), upper := (rows 31 14 7 11 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile70_node3 : Upper (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,12] 2 profile70_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30,12] 2 profile70_node3_cert).mp (by decide +kernel))

def profile70_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile70_node1 : Upper (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30] 2 (by decide) (choices 2) [5,12] profile70_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [30] (choices 2) [5,12] profile70_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile70_node2
  · exact profile70_node3

def profile70_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node0 : Upper (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [] 2 (by decide) (choices 4) [30] profile70_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [] (choices 4) [30] profile70_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node1

theorem profile70 : Upper (D (n:=5) [67,36,34,34,33]) (R (n:=5) [67,36,34,34,33]) [] 2 := profile70_node0

def profile71_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile71_node2 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,13] 2 profile71_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,13] 2 profile71_node2_cert).mp (by decide +kernel))

def profile71_node4_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 15 23 7 11 27), lower := (rows 15 23 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile71_node4 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,3] 2 profile71_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,3] 2 profile71_node4_cert).mp (by decide +kernel))

def profile71_node5_cert : CutBound 5 := { lost := (rows 0 0 2 4 4), upper := (rows 15 23 13 11 19), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile71_node5 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,9] 2 profile71_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21,9] 2 profile71_node5_cert).mp (by decide +kernel))

def profile71_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node3 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21] 2 (by decide) (choices 2) [3,9] profile71_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14,21] (choices 2) [3,9] profile71_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile71_node4
  · exact profile71_node5

def profile71_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile71_node1 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14] 2 (by decide) (choices 3) [13,21] profile71_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [14] (choices 3) [13,21] profile71_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile71_node2
  · exact profile71_node3

def profile71_node8_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 23 15 7 11 27), lower := (rows 23 15 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile71_node8 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,3] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,3] 2 profile71_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,3] 2 profile71_node8_cert).mp (by decide +kernel))

def profile71_node9_cert : CutBound 5 := { lost := (rows 0 0 2 4 4), upper := (rows 23 15 13 11 19), lower := (rows 23 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile71_node9 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,9] 2 profile71_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13,9] 2 profile71_node9_cert).mp (by decide +kernel))

def profile71_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node7 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13] 2 (by decide) (choices 2) [3,9] profile71_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22,13] (choices 2) [3,9] profile71_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile71_node8
  · exact profile71_node9

def profile71_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node6 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22] 2 (by decide) (choices 3) [13] profile71_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [22] (choices 3) [13] profile71_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node7

def profile71_node11_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 29 15 7 11 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile71_node11 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28,13] 2 profile71_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28,13] 2 profile71_node11_cert).mp (by decide +kernel))

def profile71_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node10 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28] 2 (by decide) (choices 3) [13] profile71_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [28] (choices 3) [13] profile71_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node11

def profile71_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile71_node0 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [] 2 (by decide) (choices 3) [14,22,28] profile71_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [] (choices 3) [14,22,28] profile71_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile71_node1
  · exact profile71_node6
  · exact profile71_node10

theorem profile71 : Upper (D (n:=5) [52,51,34,34,33]) (R (n:=5) [52,51,34,34,33]) [] 2 := profile71_node0

def profile72_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 3), upper := (rows 31 7 7 11 28), lower := (rows 31 7 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 11 11 11 16) }] }

theorem profile72_node4 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,3] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,3] 2 profile72_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,3] 2 profile72_node4_cert).mp (by decide +kernel))

def profile72_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 31 7 7 13 26), lower := (rows 31 7 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 25 16) }] }

theorem profile72_node5 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,5] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,5] 2 profile72_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,5] 2 profile72_node5_cert).mp (by decide +kernel))

def profile72_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 31 7 7 14 25), lower := (rows 31 7 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 10 16) }] }

theorem profile72_node6 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,6] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,6] 2 profile72_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3,6] 2 profile72_node6_cert).mp (by decide +kernel))

def profile72_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node3 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3] 2 := by
  apply routed_branch (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3] 2 (by decide) (choices 2) [3,5,6] profile72_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,3] (choices 2) [3,5,6] profile72_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile72_node4
  · exact profile72_node5
  · exact profile72_node6

def profile72_node7_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 31 7 13 15 23), lower := (rows 31 7 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile72_node7 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,9] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,9] 2 profile72_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,9] 2 profile72_node7_cert).mp (by decide +kernel))

def profile72_node8_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 31 7 14 15 23), lower := (rows 31 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 14 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile72_node8 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,10] 2 profile72_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5,10] 2 profile72_node8_cert).mp (by decide +kernel))

def profile72_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node2 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5] 2 (by decide) (choices 2) [3,9,10] profile72_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,5] (choices 2) [3,9,10] profile72_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile72_node3
  · exact profile72_node7
  · exact profile72_node8

def profile72_node9_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 31 11 7 15 23), lower := (rows 31 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile72_node9 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,9] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,9] 2 profile72_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,9] 2 profile72_node9_cert).mp (by decide +kernel))

def profile72_node10_cert : CutBound 5 := { lost := (rows 0 1 8 0 8), upper := (rows 31 14 7 15 23), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile72_node10 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,12] 2 profile72_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30,12] 2 profile72_node10_cert).mp (by decide +kernel))

def profile72_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node1 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30] 2 (by decide) (choices 2) [5,9,12] profile72_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [30] (choices 2) [5,9,12] profile72_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile72_node2
  · exact profile72_node9
  · exact profile72_node10

def profile72_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node0 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [] 2 (by decide) (choices 4) [30] profile72_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [] (choices 4) [30] profile72_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node1

theorem profile72 : Upper (D (n:=5) [67,35,35,34,33]) (R (n:=5) [67,35,35,34,33]) [] 2 := profile72_node0

def profile73_node3_cert : CutBound 5 := { lost := (rows 0 8 8 1 1), upper := (rows 31 7 7 14 30), lower := (rows 31 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile73_node3 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,3] 2 :=
  cut_bound_sound (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,3] 2 profile73_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,3] 2 profile73_node3_cert).mp (by decide +kernel))

def profile73_node4_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 31 7 14 15 23), lower := (rows 31 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 14 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile73_node4 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,10] 2 profile73_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5,10] 2 profile73_node4_cert).mp (by decide +kernel))

def profile73_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node2 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5] 2 (by decide) (choices 2) [3,10] profile73_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,5] (choices 2) [3,10] profile73_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile73_node3
  · exact profile73_node4

def profile73_node5_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 31 11 7 15 23), lower := (rows 31 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile73_node5 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,9] 2 :=
  cut_bound_sound (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,9] 2 profile73_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,9] 2 profile73_node5_cert).mp (by decide +kernel))

def profile73_node6_cert : CutBound 5 := { lost := (rows 0 1 8 0 8), upper := (rows 31 14 7 15 23), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile73_node6 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,12] 2 profile73_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30,12] 2 profile73_node6_cert).mp (by decide +kernel))

def profile73_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node1 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30] 2 (by decide) (choices 2) [5,9,12] profile73_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [30] (choices 2) [5,9,12] profile73_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node2
  · exact profile73_node5
  · exact profile73_node6

def profile73_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node0 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [] 2 (by decide) (choices 4) [30] profile73_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [] (choices 4) [30] profile73_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node1

theorem profile73 : Upper (D (n:=5) [66,36,35,34,33]) (R (n:=5) [66,36,35,34,33]) [] 2 := profile73_node0

def profile74_node3_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 15 15 7 29 21), lower := (rows 15 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile74_node3 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,3] 2 profile74_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,3] 2 profile74_node3_cert).mp (by decide +kernel))

def profile74_node5_cert : CutBound 5 := { lost := (rows 0 0 2 4 2), upper := (rows 15 15 21 11 21), lower := (rows 15 15 21 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 21 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 25 11 16) }] }

theorem profile74_node5 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,3] 2 profile74_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,3] 2 profile74_node5_cert).mp (by decide +kernel))

def profile74_node6_cert : CutBound 5 := { lost := (rows 0 0 8 2 12), upper := (rows 15 15 21 13 19), lower := (rows 15 15 21 13 16), losses := [{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 25 16) },{ target := 3, region := (rows 1 2 15 0 19), good := (rows 23 23 21 21 16) }] }

theorem profile74_node6 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,5] 2 profile74_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17,5] 2 profile74_node6_cert).mp (by decide +kernel))

def profile74_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node4 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17] 2 (by decide) (choices 2) [3,5] profile74_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13,17] (choices 2) [3,5] profile74_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node5
  · exact profile74_node6

def profile74_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node2 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13] 2 (by decide) (choices 2) [3,17] profile74_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,13] (choices 2) [3,17] profile74_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node3
  · exact profile74_node4

def profile74_node8_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 23 7 13 29), lower := (rows 15 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile74_node8 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,3] 2 profile74_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,3] 2 profile74_node8_cert).mp (by decide +kernel))

def profile74_node9_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 23 13 15 23), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile74_node9 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,9] 2 profile74_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21,9] 2 profile74_node9_cert).mp (by decide +kernel))

def profile74_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node7 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21] 2 (by decide) (choices 2) [3,9] profile74_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,21] (choices 2) [3,9] profile74_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node8
  · exact profile74_node9

def profile74_node11_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 15 27 7 13 21), lower := (rows 15 27 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile74_node11 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25,3] 2 profile74_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25,3] 2 profile74_node11_cert).mp (by decide +kernel))

def profile74_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node10 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25] 2 (by decide) (choices 2) [3] profile74_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14,25] (choices 2) [3] profile74_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node11

def profile74_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node1 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14] 2 (by decide) (choices 3) [13,21,25] profile74_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [14] (choices 3) [13,21,25] profile74_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile74_node2
  · exact profile74_node7
  · exact profile74_node10

def profile74_node14_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 23 15 7 13 29), lower := (rows 23 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile74_node14 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,3] 2 profile74_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,3] 2 profile74_node14_cert).mp (by decide +kernel))

def profile74_node15_cert : CutBound 5 := { lost := (rows 8 0 2 0 8), upper := (rows 23 15 13 15 23), lower := (rows 23 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile74_node15 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,9] 2 profile74_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13,9] 2 profile74_node15_cert).mp (by decide +kernel))

def profile74_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node13 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13] 2 (by decide) (choices 2) [3,9] profile74_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22,13] (choices 2) [3,9] profile74_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node14
  · exact profile74_node15

def profile74_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node12 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22] 2 (by decide) (choices 3) [13] profile74_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [22] (choices 3) [13] profile74_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node13

def profile74_node18_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 27 15 7 13 21), lower := (rows 27 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile74_node18 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13,3] 2 profile74_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13,3] 2 profile74_node18_cert).mp (by decide +kernel))

def profile74_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node17 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13] 2 (by decide) (choices 2) [3] profile74_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26,13] (choices 2) [3] profile74_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node18

def profile74_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node16 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26] 2 (by decide) (choices 3) [13] profile74_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [26] (choices 3) [13] profile74_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node17

def profile74_node22_cert : CutBound 5 := { lost := (rows 2 0 0 4 2), upper := (rows 29 15 7 11 21), lower := (rows 29 15 7 11 16), losses := [{ target := 1, region := (rows 3 0 4 8 23), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 14 16), good := (rows 25 11 11 11 16) }] }

theorem profile74_node22 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,3] 2 profile74_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,3] 2 profile74_node22_cert).mp (by decide +kernel))

def profile74_node23_cert : CutBound 5 := { lost := (rows 0 0 8 2 12), upper := (rows 29 15 7 13 19), lower := (rows 29 15 7 13 16), losses := [{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 25 27 19 25 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 21 16) }] }

theorem profile74_node23 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,5] 2 profile74_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3,5] 2 profile74_node23_cert).mp (by decide +kernel))

def profile74_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node21 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3] 2 (by decide) (choices 2) [3,5] profile74_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13,3] (choices 2) [3,5] profile74_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile74_node22
  · exact profile74_node23

def profile74_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node20 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13] 2 (by decide) (choices 2) [3] profile74_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28,13] (choices 2) [3] profile74_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node21

def profile74_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node19 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28] 2 (by decide) (choices 3) [13] profile74_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [28] (choices 3) [13] profile74_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node20

def profile74_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node0 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [] 2 (by decide) (choices 3) [14,22,26,28] profile74_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [] (choices 3) [14,22,26,28] profile74_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile74_node1
  · exact profile74_node12
  · exact profile74_node16
  · exact profile74_node19

theorem profile74 : Upper (D (n:=5) [52,50,35,34,33]) (R (n:=5) [52,50,35,34,33]) [] 2 := profile74_node0

def profile75_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 9), upper := (rows 15 15 7 25 22), lower := (rows 15 15 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 22 24 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile75_node4 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,17] 2 profile75_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,17] 2 profile75_node4_cert).mp (by decide +kernel))

def profile75_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 10), upper := (rows 15 15 7 26 21), lower := (rows 15 15 7 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 21 24 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile75_node5 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,18] 2 profile75_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,18] 2 profile75_node5_cert).mp (by decide +kernel))

def profile75_node6_cert : CutBound 5 := { lost := (rows 0 0 8 0 12), upper := (rows 15 15 7 28 19), lower := (rows 15 15 7 28 16), losses := [{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 19 24 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 20 16) }] }

theorem profile75_node6 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,20] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,20] 2 profile75_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3,20] 2 profile75_node6_cert).mp (by decide +kernel))

def profile75_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node3 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3] 2 (by decide) (choices 2) [17,18,20] profile75_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,3] (choices 2) [17,18,20] profile75_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node4
  · exact profile75_node5
  · exact profile75_node6

def profile75_node8_cert : CutBound 5 := { lost := (rows 0 0 8 4 9), upper := (rows 15 15 21 11 22), lower := (rows 15 15 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 26 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 25 11 16) },{ target := 3, region := (rows 1 2 15 0 27), good := (rows 23 23 21 23 16) }] }

theorem profile75_node8 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,3] 2 profile75_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,3] 2 profile75_node8_cert).mp (by decide +kernel))

def profile75_node9_cert : CutBound 5 := { lost := (rows 0 0 8 1 12), upper := (rows 15 15 21 14 19), lower := (rows 15 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 26 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 22 16) }] }

theorem profile75_node9 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,6] 2 profile75_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17,6] 2 profile75_node9_cert).mp (by decide +kernel))

def profile75_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node7 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17] 2 (by decide) (choices 2) [3,6] profile75_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,17] (choices 2) [3,6] profile75_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node8
  · exact profile75_node9

def profile75_node11_cert : CutBound 5 := { lost := (rows 0 0 8 4 10), upper := (rows 15 15 22 11 21), lower := (rows 15 15 22 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 20 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 26 11 16) },{ target := 3, region := (rows 1 2 15 0 27), good := (rows 23 23 22 23 16) }] }

theorem profile75_node11 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,3] 2 profile75_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,3] 2 profile75_node11_cert).mp (by decide +kernel))

def profile75_node12_cert : CutBound 5 := { lost := (rows 0 0 8 2 12), upper := (rows 15 15 22 13 19), lower := (rows 15 15 22 13 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 18 25 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 21 16) }] }

theorem profile75_node12 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,5] 2 profile75_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18,5] 2 profile75_node12_cert).mp (by decide +kernel))

def profile75_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node10 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18] 2 (by decide) (choices 2) [3,5] profile75_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13,18] (choices 2) [3,5] profile75_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node11
  · exact profile75_node12

def profile75_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node2 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13] 2 (by decide) (choices 2) [3,17,18] profile75_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,13] (choices 2) [3,17,18] profile75_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node3
  · exact profile75_node7
  · exact profile75_node10

def profile75_node15_cert : CutBound 5 := { lost := (rows 0 0 0 4 3), upper := (rows 15 23 7 11 28), lower := (rows 15 23 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 11 27 11 11 16) }] }

theorem profile75_node15 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,3] 2 profile75_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,3] 2 profile75_node15_cert).mp (by decide +kernel))

def profile75_node16_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 15 23 7 13 26), lower := (rows 15 23 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 25 16) }] }

theorem profile75_node16 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,5] 2 profile75_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,5] 2 profile75_node16_cert).mp (by decide +kernel))

def profile75_node17_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 15 23 7 14 25), lower := (rows 15 23 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 10 16) }] }

theorem profile75_node17 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,6] 2 profile75_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3,6] 2 profile75_node17_cert).mp (by decide +kernel))

def profile75_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node14 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3] 2 (by decide) (choices 2) [3,5,6] profile75_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,3] (choices 2) [3,5,6] profile75_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node15
  · exact profile75_node16
  · exact profile75_node17

def profile75_node18_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 23 13 15 23), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile75_node18 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,9] 2 profile75_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,9] 2 profile75_node18_cert).mp (by decide +kernel))

def profile75_node19_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 23 14 15 23), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile75_node19 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,10] 2 profile75_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21,10] 2 profile75_node19_cert).mp (by decide +kernel))

def profile75_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node13 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21] 2 (by decide) (choices 2) [3,9,10] profile75_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,21] (choices 2) [3,9,10] profile75_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node14
  · exact profile75_node18
  · exact profile75_node19

def profile75_node22_cert : CutBound 5 := { lost := (rows 0 0 8 2 9), upper := (rows 15 27 7 13 22), lower := (rows 15 27 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 25 13 13 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile75_node22 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,5] 2 profile75_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,5] 2 profile75_node22_cert).mp (by decide +kernel))

def profile75_node23_cert : CutBound 5 := { lost := (rows 0 0 8 1 10), upper := (rows 15 27 7 14 21), lower := (rows 15 27 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile75_node23 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,6] 2 profile75_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3,6] 2 profile75_node23_cert).mp (by decide +kernel))

def profile75_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node21 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3] 2 (by decide) (choices 2) [5,6] profile75_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25,3] (choices 2) [5,6] profile75_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node22
  · exact profile75_node23

def profile75_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node20 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25] 2 (by decide) (choices 2) [3] profile75_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,25] (choices 2) [3] profile75_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node21

def profile75_node26_cert : CutBound 5 := { lost := (rows 0 0 8 4 10), upper := (rows 15 30 7 11 21), lower := (rows 15 30 7 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 21 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 11 26 11 11 16) },{ target := 3, region := (rows 1 2 13 0 29), good := (rows 23 22 23 23 16) }] }

theorem profile75_node26 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,3] 2 profile75_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,3] 2 profile75_node26_cert).mp (by decide +kernel))

def profile75_node27_cert : CutBound 5 := { lost := (rows 0 0 8 2 12), upper := (rows 15 30 7 13 19), lower := (rows 15 30 7 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 19 25 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 21 16) }] }

theorem profile75_node27 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,5] 2 profile75_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3,5] 2 profile75_node27_cert).mp (by decide +kernel))

def profile75_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node25 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3] 2 (by decide) (choices 2) [3,5] profile75_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28,3] (choices 2) [3,5] profile75_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node26
  · exact profile75_node27

def profile75_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node24 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28] 2 (by decide) (choices 2) [3] profile75_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14,28] (choices 2) [3] profile75_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node25

def profile75_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node1 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile75_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [14] (choices 3) [13,21,25,28] profile75_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile75_node2
  · exact profile75_node13
  · exact profile75_node20
  · exact profile75_node24

def profile75_node31_cert : CutBound 5 := { lost := (rows 0 0 0 4 3), upper := (rows 23 15 7 11 28), lower := (rows 23 15 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 29 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 11 11 11 16) }] }

theorem profile75_node31 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,3] 2 profile75_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,3] 2 profile75_node31_cert).mp (by decide +kernel))

def profile75_node32_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 23 15 7 13 26), lower := (rows 23 15 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 22 12 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 9 16) }] }

theorem profile75_node32 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,5] 2 profile75_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,5] 2 profile75_node32_cert).mp (by decide +kernel))

def profile75_node33_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 23 15 7 14 25), lower := (rows 23 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 26 16) }] }

theorem profile75_node33 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,6] 2 profile75_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3,6] 2 profile75_node33_cert).mp (by decide +kernel))

def profile75_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node30 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3] 2 (by decide) (choices 2) [3,5,6] profile75_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,3] (choices 2) [3,5,6] profile75_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node31
  · exact profile75_node32
  · exact profile75_node33

def profile75_node34_cert : CutBound 5 := { lost := (rows 8 0 2 0 8), upper := (rows 23 15 13 15 23), lower := (rows 23 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile75_node34 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,9] 2 profile75_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,9] 2 profile75_node34_cert).mp (by decide +kernel))

def profile75_node35_cert : CutBound 5 := { lost := (rows 8 0 1 0 8), upper := (rows 23 15 14 15 23), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile75_node35 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,10] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,10] 2 profile75_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13,10] 2 profile75_node35_cert).mp (by decide +kernel))

def profile75_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node29 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13] 2 (by decide) (choices 2) [3,9,10] profile75_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22,13] (choices 2) [3,9,10] profile75_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node30
  · exact profile75_node34
  · exact profile75_node35

def profile75_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node28 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22] 2 (by decide) (choices 3) [13] profile75_node28_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [22] (choices 3) [13] profile75_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node29

def profile75_node39_cert : CutBound 5 := { lost := (rows 0 0 8 2 9), upper := (rows 27 15 7 13 22), lower := (rows 27 15 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 22 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 13 13 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile75_node39 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,5] 2 profile75_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,5] 2 profile75_node39_cert).mp (by decide +kernel))

def profile75_node40_cert : CutBound 5 := { lost := (rows 0 0 8 1 10), upper := (rows 27 15 7 14 21), lower := (rows 27 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile75_node40 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,6] 2 profile75_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3,6] 2 profile75_node40_cert).mp (by decide +kernel))

def profile75_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node38 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3] 2 (by decide) (choices 2) [5,6] profile75_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13,3] (choices 2) [5,6] profile75_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node39
  · exact profile75_node40

def profile75_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node37 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13] 2 (by decide) (choices 2) [3] profile75_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26,13] (choices 2) [3] profile75_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node38

def profile75_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node36 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26] 2 (by decide) (choices 3) [13] profile75_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [26] (choices 3) [13] profile75_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node37

def profile75_node44_cert : CutBound 5 := { lost := (rows 0 0 8 4 9), upper := (rows 29 15 7 11 22), lower := (rows 29 15 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 28 30 22 26 16) },{ target := 2, region := (rows 1 2 0 14 16), good := (rows 25 11 11 11 16) },{ target := 3, region := (rows 1 2 14 0 30), good := (rows 21 23 23 23 16) }] }

theorem profile75_node44 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,3] 2 profile75_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,3] 2 profile75_node44_cert).mp (by decide +kernel))

def profile75_node45_cert : CutBound 5 := { lost := (rows 0 0 8 1 12), upper := (rows 29 15 7 14 19), lower := (rows 29 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 28 14 14 14 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 25 27 19 26 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 22 16) }] }

theorem profile75_node45 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,6] 2 profile75_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3,6] 2 profile75_node45_cert).mp (by decide +kernel))

def profile75_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node43 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3] 2 (by decide) (choices 2) [3,6] profile75_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13,3] (choices 2) [3,6] profile75_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile75_node44
  · exact profile75_node45

def profile75_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node42 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13] 2 (by decide) (choices 2) [3] profile75_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28,13] (choices 2) [3] profile75_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node43

def profile75_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node41 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28] 2 (by decide) (choices 3) [13] profile75_node41_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [28] (choices 3) [13] profile75_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node42

def profile75_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node0 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [] 2 (by decide) (choices 3) [14,22,26,28] profile75_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [] (choices 3) [14,22,26,28] profile75_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile75_node1
  · exact profile75_node28
  · exact profile75_node36
  · exact profile75_node41

theorem profile75 : Upper (D (n:=5) [51,51,35,34,33]) (R (n:=5) [51,51,35,34,33]) [] 2 := profile75_node0

def profile76_node3_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 15 15 7 29 21), lower := (rows 15 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile76_node3 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,3] 2 profile76_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,3] 2 profile76_node3_cert).mp (by decide +kernel))

def profile76_node5_cert : CutBound 5 := { lost := (rows 0 0 8 2 9), upper := (rows 15 15 21 13 22), lower := (rows 15 15 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 13 29 13 16) },{ target := 3, region := (rows 1 2 15 0 19), good := (rows 23 23 21 21 16) }] }

theorem profile76_node5 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,5] 2 profile76_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,5] 2 profile76_node5_cert).mp (by decide +kernel))

def profile76_node6_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 15 21 14 21), lower := (rows 15 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 21 28 16) }] }

theorem profile76_node6 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,6] 2 profile76_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17,6] 2 profile76_node6_cert).mp (by decide +kernel))

def profile76_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node4 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17] 2 (by decide) (choices 2) [5,6] profile76_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,17] (choices 2) [5,6] profile76_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node5
  · exact profile76_node6

def profile76_node7_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 15 15 22 13 21), lower := (rows 15 15 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile76_node7 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,18] 2 profile76_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13,18] 2 profile76_node7_cert).mp (by decide +kernel))

def profile76_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node2 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13] 2 (by decide) (choices 2) [3,17,18] profile76_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,13] (choices 2) [3,17,18] profile76_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node3
  · exact profile76_node4
  · exact profile76_node7

def profile76_node9_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 23 7 13 29), lower := (rows 15 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile76_node9 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,3] 2 profile76_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,3] 2 profile76_node9_cert).mp (by decide +kernel))

def profile76_node10_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 23 13 15 23), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile76_node10 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,9] 2 profile76_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,9] 2 profile76_node10_cert).mp (by decide +kernel))

def profile76_node11_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 23 14 13 21), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile76_node11 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,10] 2 profile76_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21,10] 2 profile76_node11_cert).mp (by decide +kernel))

def profile76_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node8 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21] 2 (by decide) (choices 2) [3,9,10] profile76_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,21] (choices 2) [3,9,10] profile76_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node9
  · exact profile76_node10
  · exact profile76_node11

def profile76_node13_cert : CutBound 5 := { lost := (rows 0 0 8 2 10), upper := (rows 15 30 7 13 21), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile76_node13 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28,3] 2 profile76_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28,3] 2 profile76_node13_cert).mp (by decide +kernel))

def profile76_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node12 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28] 2 (by decide) (choices 2) [3] profile76_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14,28] (choices 2) [3] profile76_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node13

def profile76_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node1 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14] 2 (by decide) (choices 3) [13,21,28] profile76_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [14] (choices 3) [13,21,28] profile76_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node2
  · exact profile76_node8
  · exact profile76_node12

def profile76_node16_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 23 15 7 13 29), lower := (rows 23 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile76_node16 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,3] 2 profile76_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,3] 2 profile76_node16_cert).mp (by decide +kernel))

def profile76_node17_cert : CutBound 5 := { lost := (rows 8 0 2 0 8), upper := (rows 23 15 13 15 23), lower := (rows 23 15 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile76_node17 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,9] 2 profile76_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,9] 2 profile76_node17_cert).mp (by decide +kernel))

def profile76_node18_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 23 15 14 13 21), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile76_node18 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,10] 2 profile76_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13,10] 2 profile76_node18_cert).mp (by decide +kernel))

def profile76_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node15 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13] 2 (by decide) (choices 2) [3,9,10] profile76_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22,13] (choices 2) [3,9,10] profile76_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node16
  · exact profile76_node17
  · exact profile76_node18

def profile76_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node14 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22] 2 (by decide) (choices 3) [13] profile76_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [22] (choices 3) [13] profile76_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node15

def profile76_node22_cert : CutBound 5 := { lost := (rows 0 0 8 2 9), upper := (rows 29 15 7 13 22), lower := (rows 29 15 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 28 30 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 21 16) }] }

theorem profile76_node22 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,5] 2 profile76_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,5] 2 profile76_node22_cert).mp (by decide +kernel))

def profile76_node23_cert : CutBound 5 := { lost := (rows 2 0 0 1 2), upper := (rows 29 15 7 14 21), lower := (rows 29 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 28 14 14 14 16) },{ target := 1, region := (rows 11 0 4 8 31), good := (rows 29 29 21 29 16) }] }

theorem profile76_node23 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,6] 2 profile76_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3,6] 2 profile76_node23_cert).mp (by decide +kernel))

def profile76_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node21 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3] 2 (by decide) (choices 2) [5,6] profile76_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13,3] (choices 2) [5,6] profile76_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile76_node22
  · exact profile76_node23

def profile76_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node20 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13] 2 (by decide) (choices 2) [3] profile76_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28,13] (choices 2) [3] profile76_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node21

def profile76_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node19 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28] 2 (by decide) (choices 3) [13] profile76_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [28] (choices 3) [13] profile76_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node20

def profile76_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node0 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [] 2 (by decide) (choices 3) [14,22,28] profile76_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [] (choices 3) [14,22,28] profile76_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node1
  · exact profile76_node14
  · exact profile76_node19

theorem profile76 : Upper (D (n:=5) [51,50,36,34,33]) (R (n:=5) [51,50,36,34,33]) [] 2 := profile76_node0

#print axioms profile76
end Delivery.FiveVertexPositive12
