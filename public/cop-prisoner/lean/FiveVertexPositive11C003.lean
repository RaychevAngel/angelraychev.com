import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive11
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile33_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile33_node2 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,5] 3 profile33_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,5] 3 profile33_node2_cert).mp (by decide +kernel))

def profile33_node3_cert : CutBound 5 := { lost := (rows 0 1 0 4 4), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile33_node3 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,12] 3 profile33_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,12] 3 profile33_node3_cert).mp (by decide +kernel))

def profile33_node5_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 15 19 7 14 30), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile33_node5 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,3] 3 profile33_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,3] 3 profile33_node5_cert).mp (by decide +kernel))

def profile33_node6_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 19 14 15 23), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 0 16) }] }

theorem profile33_node6 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,10] 3 profile33_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17,10] 3 profile33_node6_cert).mp (by decide +kernel))

def profile33_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node4 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17] 3 (by decide) (choices 2) [3,10] profile33_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,17] (choices 2) [3,10] profile33_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node5
  · exact profile33_node6

def profile33_node8_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 15 22 7 11 27), lower := (rows 15 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile33_node8 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,3] 3 profile33_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,3] 3 profile33_node8_cert).mp (by decide +kernel))

def profile33_node9_cert : CutBound 5 := { lost := (rows 0 0 1 4 4), upper := (rows 15 22 14 11 19), lower := (rows 15 22 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) }] }

theorem profile33_node9 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,10] 3 profile33_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20,10] 3 profile33_node9_cert).mp (by decide +kernel))

def profile33_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node7 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20] 3 (by decide) (choices 2) [3,10] profile33_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14,20] (choices 2) [3,10] profile33_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node8
  · exact profile33_node9

def profile33_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile33_node1 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile33_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [14] (choices 2) [5,12,17,20] profile33_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile33_node2
  · exact profile33_node3
  · exact profile33_node4
  · exact profile33_node7

def profile33_node11_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 23 7 15 11 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile33_node11 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,5] 3 profile33_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,5] 3 profile33_node11_cert).mp (by decide +kernel))

def profile33_node13_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 23 11 7 14 30), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile33_node13 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,3] 3 profile33_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,3] 3 profile33_node13_cert).mp (by decide +kernel))

def profile33_node14_cert : CutBound 5 := { lost := (rows 8 0 1 0 8), upper := (rows 23 11 14 15 23), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile33_node14 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,10] 3 profile33_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9,10] 3 profile33_node14_cert).mp (by decide +kernel))

def profile33_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node12 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9] 3 (by decide) (choices 2) [3,10] profile33_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,9] (choices 2) [3,10] profile33_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node13
  · exact profile33_node14

def profile33_node16_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 23 14 7 11 27), lower := (rows 23 14 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 0 16) }] }

theorem profile33_node16 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,3] 3 profile33_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,3] 3 profile33_node16_cert).mp (by decide +kernel))

def profile33_node17_cert : CutBound 5 := { lost := (rows 0 1 1 4 4), upper := (rows 23 14 14 11 19), lower := (rows 23 14 14 8 16), losses := [{ target := 0, region := (rows 0 14 14 8 16), good := (rows 22 14 14 14 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 10 8 16) }] }

theorem profile33_node17 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,10] 3 :=
  cut_bound_sound (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,10] 3 profile33_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12,10] 3 profile33_node17_cert).mp (by decide +kernel))

def profile33_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node15 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12] 3 (by decide) (choices 2) [3,10] profile33_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22,12] (choices 2) [3,10] profile33_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node16
  · exact profile33_node17

def profile33_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node10 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22] 3 (by decide) (choices 2) [5,9,12] profile33_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [22] (choices 2) [5,9,12] profile33_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node11
  · exact profile33_node12
  · exact profile33_node15

def profile33_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile33_node0 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [] 3 := by
  apply routed_branch (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [] 3 (by decide) (choices 3) [14,22] profile33_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [] (choices 3) [14,22] profile33_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node1
  · exact profile33_node10

theorem profile33 : Upper (D (n:=5) [50,36,34,34,33]) (R (n:=5) [50,36,34,34,33]) [] 3 := profile33_node0

def profile34_node3_cert : CutBound 5 := { lost := (rows 0 8 8 1 1), upper := (rows 15 7 7 30 30), lower := (rows 15 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile34_node3 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,3] 3 profile34_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,3] 3 profile34_node3_cert).mp (by decide +kernel))

def profile34_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 15 7 13 30 22), lower := (rows 15 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 5 13 8 16) }] }

theorem profile34_node4 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,9] 3 profile34_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,9] 3 profile34_node4_cert).mp (by decide +kernel))

def profile34_node5_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 7 14 31 23), lower := (rows 15 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 6 14 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile34_node5 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,10] 3 profile34_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,10] 3 profile34_node5_cert).mp (by decide +kernel))

def profile34_node6_cert : CutBound 5 := { lost := (rows 0 8 0 1 1), upper := (rows 15 7 21 14 30), lower := (rows 15 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 7 7 23 0 16) }] }

theorem profile34_node6 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,17] 3 profile34_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,17] 3 profile34_node6_cert).mp (by decide +kernel))

def profile34_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 3), upper := (rows 15 7 22 11 28), lower := (rows 15 7 22 11 16), losses := [{ target := 0, region := (rows 0 2 15 8 25), good := (rows 30 22 22 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 20 25 16) }] }

theorem profile34_node8 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,3] 3 profile34_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,3] 3 profile34_node8_cert).mp (by decide +kernel))

def profile34_node9_cert : CutBound 5 := { lost := (rows 0 0 1 2 1), upper := (rows 15 7 22 13 26), lower := (rows 15 7 22 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 13 28 13 16) }] }

theorem profile34_node9 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,5] 3 profile34_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,5] 3 profile34_node9_cert).mp (by decide +kernel))

def profile34_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 15 7 22 14 25), lower := (rows 15 7 22 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 20 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 18 10 16) }] }

theorem profile34_node10 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,6] 3 profile34_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18,6] 3 profile34_node10_cert).mp (by decide +kernel))

def profile34_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node7 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18] 3 (by decide) (choices 2) [3,5,6] profile34_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,18] (choices 2) [3,5,6] profile34_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node8
  · exact profile34_node9
  · exact profile34_node10

def profile34_node12_cert : CutBound 5 := { lost := (rows 0 0 1 4 1), upper := (rows 15 7 28 11 22), lower := (rows 15 7 28 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 27), good := (rows 30 22 28 30 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 24 11 16) }] }

theorem profile34_node12 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,3] 3 profile34_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,3] 3 profile34_node12_cert).mp (by decide +kernel))

def profile34_node13_cert : CutBound 5 := { lost := (rows 0 8 0 1 12), upper := (rows 15 7 28 14 19), lower := (rows 15 7 28 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 24 26 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 22 16) }] }

theorem profile34_node13 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,6] 3 profile34_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24,6] 3 profile34_node13_cert).mp (by decide +kernel))

def profile34_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node11 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24] 3 (by decide) (choices 2) [3,6] profile34_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5,24] (choices 2) [3,6] profile34_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node12
  · exact profile34_node13

def profile34_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node2 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile34_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,5] (choices 2) [3,9,10,17,18,24] profile34_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node3
  · exact profile34_node4
  · exact profile34_node5
  · exact profile34_node6
  · exact profile34_node7
  · exact profile34_node11

def profile34_node14_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 15 11 23 31 23), lower := (rows 15 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 11 11 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile34_node14 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,9] 3 profile34_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,9] 3 profile34_node14_cert).mp (by decide +kernel))

def profile34_node15_cert : CutBound 5 := { lost := (rows 0 1 8 0 8), upper := (rows 15 14 23 31 23), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile34_node15 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,12] 3 profile34_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,12] 3 profile34_node15_cert).mp (by decide +kernel))

def profile34_node17_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 15 19 7 14 30), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile34_node17 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,3] 3 profile34_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,3] 3 profile34_node17_cert).mp (by decide +kernel))

def profile34_node18_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 15 19 13 14 22), lower := (rows 15 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) }] }

theorem profile34_node18 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,9] 3 profile34_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,9] 3 profile34_node18_cert).mp (by decide +kernel))

def profile34_node19_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 19 14 15 23), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 0 16) }] }

theorem profile34_node19 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,10] 3 profile34_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17,10] 3 profile34_node19_cert).mp (by decide +kernel))

def profile34_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node16 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17] 3 (by decide) (choices 2) [3,9,10] profile34_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,17] (choices 2) [3,9,10] profile34_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node17
  · exact profile34_node18
  · exact profile34_node19

def profile34_node22_cert : CutBound 5 := { lost := (rows 0 1 0 0 3), upper := (rows 15 22 7 11 28), lower := (rows 15 22 7 11 16), losses := [{ target := 0, region := (rows 0 7 4 8 17), good := (rows 30 22 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 20 21 25 16) }] }

theorem profile34_node22 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,3] 3 profile34_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,3] 3 profile34_node22_cert).mp (by decide +kernel))

def profile34_node23_cert : CutBound 5 := { lost := (rows 0 1 0 2 1), upper := (rows 15 22 7 13 26), lower := (rows 15 22 7 13 16), losses := [{ target := 0, region := (rows 0 15 4 8 25), good := (rows 30 22 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 28 13 13 16) }] }

theorem profile34_node23 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,5] 3 profile34_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,5] 3 profile34_node23_cert).mp (by decide +kernel))

def profile34_node24_cert : CutBound 5 := { lost := (rows 0 0 0 1 6), upper := (rows 15 22 7 14 25), lower := (rows 15 22 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 14 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 20 21 12 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 18 19 10 16) }] }

theorem profile34_node24 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,6] 3 profile34_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3,6] 3 profile34_node24_cert).mp (by decide +kernel))

def profile34_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node21 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3] 3 (by decide) (choices 2) [3,5,6] profile34_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,3] (choices 2) [3,5,6] profile34_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node22
  · exact profile34_node23
  · exact profile34_node24

def profile34_node25_cert : CutBound 5 := { lost := (rows 0 8 2 0 8), upper := (rows 15 22 13 15 23), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile34_node25 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,9] 3 profile34_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,9] 3 profile34_node25_cert).mp (by decide +kernel))

def profile34_node26_cert : CutBound 5 := { lost := (rows 0 8 1 0 8), upper := (rows 15 22 14 15 23), lower := (rows 15 22 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile34_node26 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,10] 3 profile34_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20,10] 3 profile34_node26_cert).mp (by decide +kernel))

def profile34_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node20 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20] 3 (by decide) (choices 2) [3,9,10] profile34_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,20] (choices 2) [3,9,10] profile34_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node21
  · exact profile34_node25
  · exact profile34_node26

def profile34_node29_cert : CutBound 5 := { lost := (rows 0 1 0 2 1), upper := (rows 15 26 7 13 22), lower := (rows 15 26 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 29), good := (rows 30 26 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 24 13 13 16) }] }

theorem profile34_node29 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,5] 3 profile34_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,5] 3 profile34_node29_cert).mp (by decide +kernel))

def profile34_node30_cert : CutBound 5 := { lost := (rows 0 0 8 1 10), upper := (rows 15 26 7 14 21), lower := (rows 15 26 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 14 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 24 21 28 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 18 23 22 16) }] }

theorem profile34_node30 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,6] 3 profile34_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3,6] 3 profile34_node30_cert).mp (by decide +kernel))

def profile34_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node28 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3] 3 (by decide) (choices 2) [5,6] profile34_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24,3] (choices 2) [5,6] profile34_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node29
  · exact profile34_node30

def profile34_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node27 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24] 3 (by decide) (choices 2) [3] profile34_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14,24] (choices 2) [3] profile34_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node28

def profile34_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node1 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile34_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [14] (choices 2) [5,9,12,17,20,24] profile34_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node2
  · exact profile34_node14
  · exact profile34_node15
  · exact profile34_node16
  · exact profile34_node20
  · exact profile34_node27

def profile34_node33_cert : CutBound 5 := { lost := (rows 0 8 0 1 1), upper := (rows 23 7 13 14 30), lower := (rows 23 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile34_node33 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,9] 3 profile34_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,9] 3 profile34_node33_cert).mp (by decide +kernel))

def profile34_node35_cert : CutBound 5 := { lost := (rows 0 0 1 0 3), upper := (rows 23 7 14 11 28), lower := (rows 23 7 14 11 16), losses := [{ target := 0, region := (rows 0 2 12 8 28), good := (rows 22 22 30 30 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 21 28 9 16) }] }

theorem profile34_node35 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,3] 3 profile34_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,3] 3 profile34_node35_cert).mp (by decide +kernel))

def profile34_node36_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 23 7 14 13 26), lower := (rows 23 7 14 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 22 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 12 13 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 19 19 26 25 16) }] }

theorem profile34_node36 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,5] 3 profile34_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,5] 3 profile34_node36_cert).mp (by decide +kernel))

def profile34_node37_cert : CutBound 5 := { lost := (rows 0 8 1 1 0), upper := (rows 23 7 14 14 25), lower := (rows 23 7 14 14 16), losses := [{ target := 0, region := (rows 0 2 15 15 16), good := (rows 30 14 14 14 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 6 6 16) }] }

theorem profile34_node37 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,6] 3 profile34_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10,6] 3 profile34_node37_cert).mp (by decide +kernel))

def profile34_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node34 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10] 3 (by decide) (choices 2) [3,5,6] profile34_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5,10] (choices 2) [3,5,6] profile34_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node35
  · exact profile34_node36
  · exact profile34_node37

def profile34_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node32 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5] 3 (by decide) (choices 2) [9,10] profile34_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,5] (choices 2) [9,10] profile34_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node33
  · exact profile34_node34

def profile34_node39_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 23 11 7 14 30), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile34_node39 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,3] 3 profile34_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,3] 3 profile34_node39_cert).mp (by decide +kernel))

def profile34_node40_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 23 11 13 14 22), lower := (rows 23 11 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) }] }

theorem profile34_node40 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,9] 3 profile34_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,9] 3 profile34_node40_cert).mp (by decide +kernel))

def profile34_node41_cert : CutBound 5 := { lost := (rows 8 0 1 0 8), upper := (rows 23 11 14 15 23), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile34_node41 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,10] 3 profile34_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9,10] 3 profile34_node41_cert).mp (by decide +kernel))

def profile34_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node38 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9] 3 (by decide) (choices 2) [3,9,10] profile34_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,9] (choices 2) [3,9,10] profile34_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node39
  · exact profile34_node40
  · exact profile34_node41

def profile34_node44_cert : CutBound 5 := { lost := (rows 0 0 0 4 3), upper := (rows 23 14 7 11 28), lower := (rows 23 14 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 28 21 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 10 11 11 16) }] }

theorem profile34_node44 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,3] 3 profile34_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,3] 3 profile34_node44_cert).mp (by decide +kernel))

def profile34_node45_cert : CutBound 5 := { lost := (rows 0 1 0 2 1), upper := (rows 23 14 7 13 26), lower := (rows 23 14 7 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 26), good := (rows 22 30 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 12 13 13 16) }] }

theorem profile34_node45 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,5] 3 profile34_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,5] 3 profile34_node45_cert).mp (by decide +kernel))

def profile34_node46_cert : CutBound 5 := { lost := (rows 0 1 8 1 0), upper := (rows 23 14 7 14 25), lower := (rows 23 14 7 14 16), losses := [{ target := 0, region := (rows 0 15 4 15 16), good := (rows 30 14 14 14 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 6 7 6 16) }] }

theorem profile34_node46 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,6] 3 profile34_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3,6] 3 profile34_node46_cert).mp (by decide +kernel))

def profile34_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node43 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3] 3 (by decide) (choices 2) [3,5,6] profile34_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,3] (choices 2) [3,5,6] profile34_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node44
  · exact profile34_node45
  · exact profile34_node46

def profile34_node47_cert : CutBound 5 := { lost := (rows 8 1 0 0 8), upper := (rows 23 14 13 15 23), lower := (rows 23 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 14 14 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile34_node47 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,9] 3 profile34_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,9] 3 profile34_node47_cert).mp (by decide +kernel))

def profile34_node48_cert : CutBound 5 := { lost := (rows 8 1 1 0 8), upper := (rows 23 14 14 15 23), lower := (rows 23 14 14 8 16), losses := [{ target := 0, region := (rows 0 14 14 8 16), good := (rows 22 14 14 14 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile34_node48 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,10] 3 profile34_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12,10] 3 profile34_node48_cert).mp (by decide +kernel))

def profile34_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node42 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12] 3 (by decide) (choices 2) [3,9,10] profile34_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22,12] (choices 2) [3,9,10] profile34_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node43
  · exact profile34_node47
  · exact profile34_node48

def profile34_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node31 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22] 3 (by decide) (choices 2) [5,9,12] profile34_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [22] (choices 2) [5,9,12] profile34_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node32
  · exact profile34_node38
  · exact profile34_node42

def profile34_node51_cert : CutBound 5 := { lost := (rows 0 8 8 1 1), upper := (rows 27 7 7 14 30), lower := (rows 27 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile34_node51 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,3] 3 profile34_node51_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,3] 3 profile34_node51_cert).mp (by decide +kernel))

def profile34_node52_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 27 7 13 14 22), lower := (rows 27 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 12 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) }] }

theorem profile34_node52 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,9] 3 profile34_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,9] 3 profile34_node52_cert).mp (by decide +kernel))

def profile34_node54_cert : CutBound 5 := { lost := (rows 0 0 1 2 1), upper := (rows 27 7 14 13 22), lower := (rows 27 7 14 13 16), losses := [{ target := 0, region := (rows 0 2 5 8 23), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 25 13 12 13 16) }] }

theorem profile34_node54 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,5] 3 profile34_node54_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,5] 3 profile34_node54_cert).mp (by decide +kernel))

def profile34_node55_cert : CutBound 5 := { lost := (rows 0 0 1 1 2), upper := (rows 27 7 14 14 21), lower := (rows 27 7 14 14 16), losses := [{ target := 0, region := (rows 0 2 15 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 25 21 28 28 16) }] }

theorem profile34_node55 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,6] 3 profile34_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10,6] 3 profile34_node55_cert).mp (by decide +kernel))

def profile34_node53_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node53 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10] 3 (by decide) (choices 2) [5,6] profile34_node53_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5,10] (choices 2) [5,6] profile34_node53_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node54
  · exact profile34_node55

def profile34_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node50 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5] 3 (by decide) (choices 2) [3,9,10] profile34_node50_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,5] (choices 2) [3,9,10] profile34_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node51
  · exact profile34_node52
  · exact profile34_node53

def profile34_node58_cert : CutBound 5 := { lost := (rows 0 1 0 2 1), upper := (rows 27 14 7 13 22), lower := (rows 27 14 7 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 30), good := (rows 26 30 22 30 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 25 12 13 13 16) }] }

theorem profile34_node58 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,5] 3 profile34_node58_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,5] 3 profile34_node58_cert).mp (by decide +kernel))

def profile34_node59_cert : CutBound 5 := { lost := (rows 0 1 0 1 2), upper := (rows 27 14 7 14 21), lower := (rows 27 14 7 14 16), losses := [{ target := 0, region := (rows 0 14 4 14 16), good := (rows 26 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 25 28 21 28 16) }] }

theorem profile34_node59 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,6] 3 profile34_node59_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3,6] 3 profile34_node59_cert).mp (by decide +kernel))

def profile34_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node57 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3] 3 (by decide) (choices 2) [5,6] profile34_node57_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12,3] (choices 2) [5,6] profile34_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node58
  · exact profile34_node59

def profile34_node56_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node56 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12] 3 (by decide) (choices 2) [3] profile34_node56_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26,12] (choices 2) [3] profile34_node56_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node57

def profile34_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node49 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26] 3 (by decide) (choices 2) [5,12] profile34_node49_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [26] (choices 2) [5,12] profile34_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node50
  · exact profile34_node56

def profile34_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile34_node0 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [] 3 := by
  apply routed_branch (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [] 3 (by decide) (choices 3) [14,22,26] profile34_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [] (choices 3) [14,22,26] profile34_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node1
  · exact profile34_node31
  · exact profile34_node49

theorem profile34 : Upper (D (n:=5) [50,35,35,34,33]) (R (n:=5) [50,35,35,34,33]) [] 3 := profile34_node0

def profile35_node4_cert : CutBound 5 := { lost := (rows 0 8 10 6 5), upper := (rows 15 7 21 25 26), lower := (rows 15 7 21 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 20 24 16) },{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 13 29 29 16) },{ target := 2, region := (rows 1 2 0 15 19), good := (rows 27 27 25 25 16) },{ target := 3, region := (rows 1 15 12 0 16), good := (rows 7 7 23 23 16) }] }

theorem profile35_node4 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,17] 3 profile35_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,17] 3 profile35_node4_cert).mp (by decide +kernel))

def profile35_node5_cert : CutBound 5 := { lost := (rows 0 24 2 4 6), upper := (rows 15 7 21 26 25), lower := (rows 15 7 21 26 16), losses := [{ target := 1, region := (rows 1 0 7 8 17), good := (rows 29 21 21 28 16) },{ target := 2, region := (rows 1 2 0 11 23), good := (rows 27 27 25 26 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 7 7 23 18 16) },{ target := 4, region := (rows 1 7 4 8 0), good := (rows 15 7 7 10 0) }] }

theorem profile35_node5 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,18] 3 profile35_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17,18] 3 profile35_node5_cert).mp (by decide +kernel))

def profile35_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node3 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17] 3 (by decide) (choices 2) [17,18] profile35_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,17] (choices 2) [17,18] profile35_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile35_node4
  · exact profile35_node5

def profile35_node6_cert : CutBound 5 := { lost := (rows 0 24 0 6 6), upper := (rows 15 7 22 25 25), lower := (rows 15 7 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 22 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 6 8 0) }] }

theorem profile35_node6 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,18] 3 profile35_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,18] 3 profile35_node6_cert).mp (by decide +kernel))

def profile35_node7_cert : CutBound 5 := { lost := (rows 16 24 0 4 12), upper := (rows 15 7 28 27 19), lower := (rows 15 7 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 5 7 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile35_node7 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,24] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,24] 3 profile35_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5,24] 3 profile35_node7_cert).mp (by decide +kernel))

def profile35_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node2 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5] 3 (by decide) (choices 2) [17,18,24] profile35_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,5] (choices 2) [17,18,24] profile35_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node3
  · exact profile35_node6
  · exact profile35_node7

def profile35_node8_cert : CutBound 5 := { lost := (rows 16 17 8 4 12), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile35_node8 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,12] 3 profile35_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,12] 3 profile35_node8_cert).mp (by decide +kernel))

def profile35_node11_cert : CutBound 5 := { lost := (rows 0 12 8 6 3), upper := (rows 15 19 7 25 28), lower := (rows 15 19 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 22 24 16) },{ target := 1, region := (rows 1 0 4 15 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 11 27 16) },{ target := 3, region := (rows 1 10 15 0 16), good := (rows 7 23 7 23 16) }] }

theorem profile35_node11 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,17] 3 profile35_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,17] 3 profile35_node11_cert).mp (by decide +kernel))

def profile35_node12_cert : CutBound 5 := { lost := (rows 0 4 24 2 6), upper := (rows 15 19 7 28 25), lower := (rows 15 19 7 28 16), losses := [{ target := 1, region := (rows 1 0 4 13 23), good := (rows 29 25 29 28 16) },{ target := 2, region := (rows 1 7 0 8 17), good := (rows 27 19 19 26 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 20 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 12 0) }] }

theorem profile35_node12 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,20] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,20] 3 profile35_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3,20] 3 profile35_node12_cert).mp (by decide +kernel))

def profile35_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node10 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3] 3 (by decide) (choices 2) [17,20] profile35_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,3] (choices 2) [17,20] profile35_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile35_node11
  · exact profile35_node12

def profile35_node14_cert : CutBound 5 := { lost := (rows 0 12 2 6 9), upper := (rows 15 19 13 25 22), lower := (rows 15 19 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 28 24 16) },{ target := 1, region := (rows 1 0 15 10 16), good := (rows 13 29 13 29 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 11 27 16) },{ target := 3, region := (rows 1 15 4 0 21), good := (rows 23 19 23 19 16) }] }

theorem profile35_node14 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,17] 3 profile35_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,17] 3 profile35_node14_cert).mp (by decide +kernel))

def profile35_node15_cert : CutBound 5 := { lost := (rows 0 8 2 5 10), upper := (rows 15 19 13 26 21), lower := (rows 15 19 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 26 12 26 16) },{ target := 1, region := (rows 1 0 5 8 23), good := (rows 29 21 29 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 9 26 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 19 23 18 16) }] }

theorem profile35_node15 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,18] 3 profile35_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,18] 3 profile35_node15_cert).mp (by decide +kernel))

def profile35_node16_cert : CutBound 5 := { lost := (rows 0 12 2 2 12), upper := (rows 15 19 13 28 19), lower := (rows 15 19 13 28 16), losses := [{ target := 1, region := (rows 1 0 7 10 16), good := (rows 13 29 13 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 19 27 26 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 19 23 22 16) }] }

theorem profile35_node16 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,20] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,20] 3 profile35_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9,20] 3 profile35_node16_cert).mp (by decide +kernel))

def profile35_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node13 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9] 3 (by decide) (choices 2) [17,18,20] profile35_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,9] (choices 2) [17,18,20] profile35_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node14
  · exact profile35_node15
  · exact profile35_node16

def profile35_node17_cert : CutBound 5 := { lost := (rows 16 8 17 2 10), upper := (rows 15 19 14 29 21), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile35_node17 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,10] 3 profile35_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,10] 3 profile35_node17_cert).mp (by decide +kernel))

def profile35_node19_cert : CutBound 5 := { lost := (rows 0 12 10 4 3), upper := (rows 15 19 21 11 28), lower := (rows 15 19 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 20 26 16) },{ target := 1, region := (rows 1 0 15 8 25), good := (rows 29 21 21 29 16) },{ target := 2, region := (rows 1 6 0 15 16), good := (rows 11 27 27 11 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile35_node19 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,3] 3 profile35_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,3] 3 profile35_node19_cert).mp (by decide +kernel))

def profile35_node20_cert : CutBound 5 := { lost := (rows 0 12 10 2 5), upper := (rows 15 19 21 13 26), lower := (rows 15 19 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 18 20 28 16) },{ target := 1, region := (rows 1 0 6 15 16), good := (rows 13 29 29 13 16) },{ target := 2, region := (rows 1 15 0 8 25), good := (rows 27 19 19 27 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 7 16) }] }

theorem profile35_node20 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,5] 3 profile35_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,5] 3 profile35_node20_cert).mp (by decide +kernel))

def profile35_node21_cert : CutBound 5 := { lost := (rows 0 12 10 1 6), upper := (rows 15 19 21 14 25), lower := (rows 15 19 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 28 14 16) },{ target := 1, region := (rows 1 0 7 8 17), good := (rows 29 21 21 12 16) },{ target := 2, region := (rows 1 7 0 8 17), good := (rows 27 19 19 10 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 6 16) }] }

theorem profile35_node21 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,6] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,6] 3 profile35_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17,6] 3 profile35_node21_cert).mp (by decide +kernel))

def profile35_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node18 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17] 3 (by decide) (choices 2) [3,5,6] profile35_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,17] (choices 2) [3,5,6] profile35_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node19
  · exact profile35_node20
  · exact profile35_node21

def profile35_node22_cert : CutBound 5 := { lost := (rows 16 0 9 18 2), upper := (rows 15 19 22 13 29), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile35_node22 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,18] 3 profile35_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,18] 3 profile35_node22_cert).mp (by decide +kernel))

def profile35_node24_cert : CutBound 5 := { lost := (rows 0 8 2 20 10), upper := (rows 15 19 28 11 21), lower := (rows 15 19 28 11 16), losses := [{ target := 1, region := (rows 1 0 13 8 27), good := (rows 29 21 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) },{ target := 3, region := (rows 1 11 4 0 17), good := (rows 23 19 22 19 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 11 12 11 0) }] }

theorem profile35_node24 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,3] 3 profile35_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,3] 3 profile35_node24_cert).mp (by decide +kernel))

def profile35_node25_cert : CutBound 5 := { lost := (rows 0 12 2 2 12), upper := (rows 15 19 28 13 19), lower := (rows 15 19 28 13 16), losses := [{ target := 1, region := (rows 1 0 6 11 16), good := (rows 13 29 28 13 16) },{ target := 2, region := (rows 1 11 0 8 27), good := (rows 27 19 26 27 16) },{ target := 3, region := (rows 1 11 4 0 27), good := (rows 23 19 22 23 16) }] }

theorem profile35_node25 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,5] 3 profile35_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24,5] 3 profile35_node25_cert).mp (by decide +kernel))

def profile35_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node23 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24] 3 (by decide) (choices 2) [3,5] profile35_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17,24] (choices 2) [3,5] profile35_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile35_node24
  · exact profile35_node25

def profile35_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node9 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile35_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,17] (choices 2) [3,9,10,17,18,24] profile35_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile35_node10
  · exact profile35_node13
  · exact profile35_node17
  · exact profile35_node18
  · exact profile35_node22
  · exact profile35_node23

def profile35_node27_cert : CutBound 5 := { lost := (rows 0 0 24 6 6), upper := (rows 15 22 7 25 25), lower := (rows 15 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 7 8 0) }] }

theorem profile35_node27 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,3] 3 profile35_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,3] 3 profile35_node27_cert).mp (by decide +kernel))

def profile35_node28_cert : CutBound 5 := { lost := (rows 0 8 18 4 12), upper := (rows 15 22 13 27 19), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 13 8 0) }] }

theorem profile35_node28 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,9] 3 profile35_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,9] 3 profile35_node28_cert).mp (by decide +kernel))

def profile35_node29_cert : CutBound 5 := { lost := (rows 16 9 0 20 4), upper := (rows 15 22 21 11 27), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile35_node29 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,17] 3 profile35_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20,17] 3 profile35_node29_cert).mp (by decide +kernel))

def profile35_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node26 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20] 3 (by decide) (choices 2) [3,9,17] profile35_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14,20] (choices 2) [3,9,17] profile35_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node27
  · exact profile35_node28
  · exact profile35_node29

def profile35_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile35_node1 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile35_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [14] (choices 2) [5,12,17,20] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile35_node2
  · exact profile35_node8
  · exact profile35_node9
  · exact profile35_node26

def profile35_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 28 => (14,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | _ => (mask,id))

theorem profile35_node0 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [] 3 (by decide) (choices 3) [14] profile35_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [] (choices 3) [14] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=5) [51,34,34,34,34]) (R (n:=5) [51,34,34,34,34]) [] 3 := profile35_node0

def profile36_node3_cert : CutBound 5 := { lost := (rows 0 24 0 5 5), upper := (rows 15 7 21 26 26), lower := (rows 15 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 16), good := (rows 7 7 23 0 16) },{ target := 4, region := (rows 1 7 4 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile36_node3 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,17] 3 profile36_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,17] 3 profile36_node3_cert).mp (by decide +kernel))

def profile36_node5_cert : CutBound 5 := { lost := (rows 0 8 9 4 5), upper := (rows 15 7 22 25 26), lower := (rows 15 7 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 17), good := (rows 30 22 22 28 16) },{ target := 2, region := (rows 1 2 0 11 23), good := (rows 27 27 26 25 16) },{ target := 3, region := (rows 1 11 12 0 16), good := (rows 7 7 22 23 16) }] }

theorem profile36_node5 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,17] 3 profile36_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,17] 3 profile36_node5_cert).mp (by decide +kernel))

def profile36_node6_cert : CutBound 5 := { lost := (rows 0 8 9 5 6), upper := (rows 15 7 22 26 25), lower := (rows 15 7 22 26 16), losses := [{ target := 0, region := (rows 0 2 12 12 16), good := (rows 14 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 20 24 16) },{ target := 2, region := (rows 1 2 0 15 19), good := (rows 27 27 26 26 16) },{ target := 3, region := (rows 1 3 12 0 16), good := (rows 7 7 22 22 16) }] }

theorem profile36_node6 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,18] 3 profile36_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18,18] 3 profile36_node6_cert).mp (by decide +kernel))

def profile36_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node4 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18] 3 (by decide) (choices 2) [17,18] profile36_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,18] (choices 2) [17,18] profile36_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node5
  · exact profile36_node6

def profile36_node7_cert : CutBound 5 := { lost := (rows 16 24 0 4 12), upper := (rows 15 7 28 27 19), lower := (rows 15 7 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 5 7 4 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile36_node7 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,24] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,24] 3 profile36_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5,24] 3 profile36_node7_cert).mp (by decide +kernel))

def profile36_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node2 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5] 3 (by decide) (choices 2) [17,18,24] profile36_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,5] (choices 2) [17,18,24] profile36_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node3
  · exact profile36_node4
  · exact profile36_node7

def profile36_node8_cert : CutBound 5 := { lost := (rows 16 17 8 4 12), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile36_node8 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,12] 3 profile36_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,12] 3 profile36_node8_cert).mp (by decide +kernel))

def profile36_node11_cert : CutBound 5 := { lost := (rows 16 0 24 5 3), upper := (rows 15 19 7 26 28), lower := (rows 15 19 7 26 16), losses := [{ target := 0, region := (rows 0 2 4 15 21), good := (rows 30 26 30 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 21 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 26 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 22 16) },{ target := 4, region := (rows 9 2 15 8 0), good := (rows 15 7 7 15 0) }] }

theorem profile36_node11 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,18] 3 profile36_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,18] 3 profile36_node11_cert).mp (by decide +kernel))

def profile36_node12_cert : CutBound 5 := { lost := (rows 0 4 24 1 5), upper := (rows 15 19 7 28 26), lower := (rows 15 19 7 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 23), good := (rows 30 26 30 28 16) },{ target := 2, region := (rows 1 7 0 8 25), good := (rows 27 19 19 26 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 20 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 12 0) }] }

theorem profile36_node12 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,20] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,20] 3 profile36_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3,20] 3 profile36_node12_cert).mp (by decide +kernel))

def profile36_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node10 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3] 3 (by decide) (choices 2) [18,20] profile36_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,3] (choices 2) [18,20] profile36_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node11
  · exact profile36_node12

def profile36_node13_cert : CutBound 5 := { lost := (rows 0 8 18 1 9), upper := (rows 15 19 13 30 22), lower := (rows 15 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile36_node13 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,9] 3 profile36_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,9] 3 profile36_node13_cert).mp (by decide +kernel))

def profile36_node15_cert : CutBound 5 := { lost := (rows 0 12 1 6 9), upper := (rows 15 19 14 25 22), lower := (rows 15 19 14 25 16), losses := [{ target := 0, region := (rows 0 2 5 8 23), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 25 12 25 16) },{ target := 2, region := (rows 1 10 0 10 16), good := (rows 11 27 10 27 16) },{ target := 3, region := (rows 1 11 4 0 21), good := (rows 23 19 22 19 16) }] }

theorem profile36_node15 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,17] 3 profile36_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,17] 3 profile36_node15_cert).mp (by decide +kernel))

def profile36_node16_cert : CutBound 5 := { lost := (rows 0 8 1 5 10), upper := (rows 15 19 14 26 21), lower := (rows 15 19 14 26 16), losses := [{ target := 0, region := (rows 0 2 15 10 16), good := (rows 14 30 14 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 12 24 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 10 26 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 6 18 16) }] }

theorem profile36_node16 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,18] 3 profile36_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,18] 3 profile36_node16_cert).mp (by decide +kernel))

def profile36_node17_cert : CutBound 5 := { lost := (rows 0 12 1 1 12), upper := (rows 15 19 14 28 19), lower := (rows 15 19 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 10 16), good := (rows 14 30 14 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 19 26 24 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 19 22 20 16) }] }

theorem profile36_node17 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,20] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,20] 3 profile36_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10,20] 3 profile36_node17_cert).mp (by decide +kernel))

def profile36_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node14 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10] 3 (by decide) (choices 2) [17,18,20] profile36_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,10] (choices 2) [17,18,20] profile36_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node15
  · exact profile36_node16
  · exact profile36_node17

def profile36_node18_cert : CutBound 5 := { lost := (rows 0 12 10 1 1), upper := (rows 15 19 21 14 30), lower := (rows 15 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 19 19 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile36_node18 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,17] 3 profile36_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,17] 3 profile36_node18_cert).mp (by decide +kernel))

def profile36_node20_cert : CutBound 5 := { lost := (rows 16 0 9 20 3), upper := (rows 15 19 22 11 28), lower := (rows 15 19 22 11 16), losses := [{ target := 0, region := (rows 0 2 15 8 25), good := (rows 30 22 22 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 20 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 26 11 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 7 16) },{ target := 4, region := (rows 5 2 4 15 0), good := (rows 15 11 15 11 0) }] }

theorem profile36_node20 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,3] 3 profile36_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,3] 3 profile36_node20_cert).mp (by decide +kernel))

def profile36_node21_cert : CutBound 5 := { lost := (rows 0 4 9 2 5), upper := (rows 15 19 22 13 26), lower := (rows 15 19 22 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 13 25 20 13 16) },{ target := 2, region := (rows 1 11 0 8 25), good := (rows 27 19 18 27 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 5 16) }] }

theorem profile36_node21 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,5] 3 profile36_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,5] 3 profile36_node21_cert).mp (by decide +kernel))

def profile36_node22_cert : CutBound 5 := { lost := (rows 0 4 9 1 6), upper := (rows 15 19 22 14 25), lower := (rows 15 19 22 14 16), losses := [{ target := 0, region := (rows 0 2 6 15 16), good := (rows 14 30 30 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 17 20 12 16) },{ target := 2, region := (rows 1 3 0 8 17), good := (rows 27 19 18 10 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 6 16) }] }

theorem profile36_node22 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,6] 3 profile36_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18,6] 3 profile36_node22_cert).mp (by decide +kernel))

def profile36_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node19 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18] 3 (by decide) (choices 2) [3,5,6] profile36_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,18] (choices 2) [3,5,6] profile36_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node20
  · exact profile36_node21
  · exact profile36_node22

def profile36_node24_cert : CutBound 5 := { lost := (rows 0 8 1 20 9), upper := (rows 15 19 28 11 22), lower := (rows 15 19 28 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 27), good := (rows 30 22 28 30 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 24 11 16) },{ target := 3, region := (rows 1 11 4 0 21), good := (rows 23 19 22 19 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 11 12 11 0) }] }

theorem profile36_node24 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,3] 3 profile36_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,3] 3 profile36_node24_cert).mp (by decide +kernel))

def profile36_node25_cert : CutBound 5 := { lost := (rows 0 12 1 1 12), upper := (rows 15 19 28 14 19), lower := (rows 15 19 28 14 16), losses := [{ target := 0, region := (rows 0 2 6 11 16), good := (rows 14 30 28 14 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 19 24 26 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 19 20 22 16) }] }

theorem profile36_node25 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,6] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,6] 3 profile36_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24,6] 3 profile36_node25_cert).mp (by decide +kernel))

def profile36_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node23 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24] 3 (by decide) (choices 2) [3,6] profile36_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17,24] (choices 2) [3,6] profile36_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node24
  · exact profile36_node25

def profile36_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node9 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile36_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,17] (choices 2) [3,9,10,17,18,24] profile36_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node10
  · exact profile36_node13
  · exact profile36_node14
  · exact profile36_node18
  · exact profile36_node19
  · exact profile36_node23

def profile36_node28_cert : CutBound 5 := { lost := (rows 0 9 8 4 5), upper := (rows 15 22 7 25 26), lower := (rows 15 22 7 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 25), good := (rows 30 22 22 26 16) },{ target := 2, region := (rows 1 2 0 13 23), good := (rows 27 26 27 25 16) },{ target := 3, region := (rows 1 10 13 0 16), good := (rows 7 22 7 23 16) }] }

theorem profile36_node28 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,17] 3 profile36_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,17] 3 profile36_node28_cert).mp (by decide +kernel))

def profile36_node29_cert : CutBound 5 := { lost := (rows 16 0 24 5 6), upper := (rows 15 22 7 26 25), lower := (rows 15 22 7 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 20 21 24 16) },{ target := 2, region := (rows 1 2 0 15 21), good := (rows 27 26 27 26 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 18 16) },{ target := 4, region := (rows 9 2 13 8 0), good := (rows 15 6 7 15 0) }] }

theorem profile36_node29 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,18] 3 profile36_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3,18] 3 profile36_node29_cert).mp (by decide +kernel))

def profile36_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node27 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3] 3 (by decide) (choices 2) [17,18] profile36_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,3] (choices 2) [17,18] profile36_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node28
  · exact profile36_node29

def profile36_node30_cert : CutBound 5 := { lost := (rows 0 8 18 4 12), upper := (rows 15 22 13 27 19), lower := (rows 15 22 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 20 13 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 7 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 13 8 0) }] }

theorem profile36_node30 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,9] 3 profile36_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,9] 3 profile36_node30_cert).mp (by decide +kernel))

def profile36_node31_cert : CutBound 5 := { lost := (rows 16 8 17 4 12), upper := (rows 15 22 14 27 19), lower := (rows 15 22 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile36_node31 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,10] 3 profile36_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,10] 3 profile36_node31_cert).mp (by decide +kernel))

def profile36_node32_cert : CutBound 5 := { lost := (rows 16 9 0 20 4), upper := (rows 15 22 21 11 27), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 22 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile36_node32 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,17] 3 profile36_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,17] 3 profile36_node32_cert).mp (by decide +kernel))

def profile36_node33_cert : CutBound 5 := { lost := (rows 0 9 9 4 4), upper := (rows 15 22 22 11 27), lower := (rows 15 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 18 8 16) },{ target := 3, region := (rows 1 22 22 0 16), good := (rows 7 22 22 0 22) }] }

theorem profile36_node33 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,18] 3 profile36_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,18] 3 profile36_node33_cert).mp (by decide +kernel))

def profile36_node34_cert : CutBound 5 := { lost := (rows 16 9 0 20 12), upper := (rows 15 22 28 11 19), lower := (rows 15 22 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 24 8 16) },{ target := 3, region := (rows 1 7 4 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile36_node34 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,24] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,24] 3 profile36_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20,24] 3 profile36_node34_cert).mp (by decide +kernel))

def profile36_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node26 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile36_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14,20] (choices 2) [3,9,10,17,18,24] profile36_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile36_node27
  · exact profile36_node30
  · exact profile36_node31
  · exact profile36_node32
  · exact profile36_node33
  · exact profile36_node34

def profile36_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile36_node1 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile36_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [14] (choices 2) [5,12,17,20] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile36_node2
  · exact profile36_node8
  · exact profile36_node9
  · exact profile36_node26

def profile36_node37_cert : CutBound 5 := { lost := (rows 0 8 8 5 5), upper := (rows 29 7 7 26 26), lower := (rows 29 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) },{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile36_node37 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,3] 3 profile36_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,3] 3 profile36_node37_cert).mp (by decide +kernel))

def profile36_node38_cert : CutBound 5 := { lost := (rows 0 24 16 4 12), upper := (rows 29 7 14 27 19), lower := (rows 29 7 14 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile36_node38 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,10] 3 profile36_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5,10] 3 profile36_node38_cert).mp (by decide +kernel))

def profile36_node36_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile36_node36 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5] 3 (by decide) (choices 2) [3,10] profile36_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,5] (choices 2) [3,10] profile36_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node37
  · exact profile36_node38

def profile36_node40_cert : CutBound 5 := { lost := (rows 0 17 16 4 12), upper := (rows 29 14 7 27 19), lower := (rows 29 14 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 6 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 21 22 23 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 14 7 8 0) }] }

theorem profile36_node40 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,3] 3 profile36_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,3] 3 profile36_node40_cert).mp (by decide +kernel))

def profile36_node42_cert : CutBound 5 := { lost := (rows 0 17 9 16 12), upper := (rows 29 14 22 11 19), lower := (rows 29 14 22 11 16), losses := [{ target := 0, region := (rows 0 11 5 8 16), good := (rows 30 14 22 14 16) },{ target := 2, region := (rows 1 2 0 8 24), good := (rows 25 26 18 27 16) },{ target := 3, region := (rows 1 2 14 0 24), good := (rows 21 22 22 23 16) },{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 14 6 11 0) }] }

theorem profile36_node42 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18,3] 3 profile36_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18,3] 3 profile36_node42_cert).mp (by decide +kernel))

def profile36_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node41 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18] 3 (by decide) (choices 2) [3] profile36_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12,18] (choices 2) [3] profile36_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node42

def profile36_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node39 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12] 3 (by decide) (choices 2) [3,18] profile36_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28,12] (choices 2) [3,18] profile36_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node40
  · exact profile36_node41

def profile36_node35_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile36_node35 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28] 3 (by decide) (choices 2) [5,12] profile36_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [28] (choices 2) [5,12] profile36_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node36
  · exact profile36_node39

def profile36_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile36_node0 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [] 3 (by decide) (choices 3) [14,28] profile36_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [] (choices 3) [14,28] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node1
  · exact profile36_node35

theorem profile36 : Upper (D (n:=5) [50,35,34,34,34]) (R (n:=5) [50,35,34,34,34]) [] 3 := profile36_node0

def profile37_node2_cert : CutBound 5 := { lost := (rows 0 8 0 4 4), upper := (rows 15 7 30 26 26), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 7 7 4 0 16) }] }

theorem profile37_node2 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,5] 3 profile37_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,5] 3 profile37_node2_cert).mp (by decide +kernel))

def profile37_node3_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) }] }

theorem profile37_node3 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,12] 3 profile37_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,12] 3 profile37_node3_cert).mp (by decide +kernel))

def profile37_node5_cert : CutBound 5 := { lost := (rows 16 8 16 0 8), upper := (rows 15 19 14 30 22), lower := (rows 15 19 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 21), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile37_node5 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,10] 3 profile37_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,10] 3 profile37_node5_cert).mp (by decide +kernel))

def profile37_node6_cert : CutBound 5 := { lost := (rows 16 0 8 16 0), upper := (rows 15 19 22 14 30), lower := (rows 15 19 22 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile37_node6 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,18] 3 profile37_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17,18] 3 profile37_node6_cert).mp (by decide +kernel))

def profile37_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node4 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17] 3 (by decide) (choices 2) [10,18] profile37_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,17] (choices 2) [10,18] profile37_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile37_node5
  · exact profile37_node6

def profile37_node8_cert : CutBound 5 := { lost := (rows 0 0 8 4 4), upper := (rows 15 22 7 26 26), lower := (rows 15 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile37_node8 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,3] 3 profile37_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,3] 3 profile37_node8_cert).mp (by decide +kernel))

def profile37_node9_cert : CutBound 5 := { lost := (rows 0 8 0 4 12), upper := (rows 15 22 14 27 19), lower := (rows 15 22 14 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 10 8 16) },{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 22 6 0 16) }] }

theorem profile37_node9 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,10] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,10] 3 profile37_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,10] 3 profile37_node9_cert).mp (by decide +kernel))

def profile37_node10_cert : CutBound 5 := { lost := (rows 0 8 8 4 4), upper := (rows 15 22 22 11 27), lower := (rows 15 22 22 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 18 8 16) },{ target := 3, region := (rows 1 22 22 0 16), good := (rows 7 22 22 0 22) }] }

theorem profile37_node10 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,18] 3 profile37_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20,18] 3 profile37_node10_cert).mp (by decide +kernel))

def profile37_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node7 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20] 3 (by decide) (choices 2) [3,10,18] profile37_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14,20] (choices 2) [3,10,18] profile37_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node8
  · exact profile37_node9
  · exact profile37_node10

def profile37_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile37_node1 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14] 3 := by
  apply routed_branch (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile37_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [14] (choices 2) [5,12,17,20] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile37_node2
  · exact profile37_node3
  · exact profile37_node4
  · exact profile37_node7

def profile37_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile37_node0 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [] 3 := by
  apply routed_branch (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [] 3 (by decide) (choices 3) [14] profile37_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [] (choices 3) [14] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=5) [49,36,34,34,34]) (R (n:=5) [49,36,34,34,34]) [] 3 := profile37_node0

#print axioms profile37
end Delivery.FiveVertexPositive11
