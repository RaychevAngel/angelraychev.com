import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,5] 3 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,5] 3 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) }] }

theorem profile0_node3 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,12] 3 profile0_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,12] 3 profile0_node3_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 19 7 13 29), lower := (rows 15 19 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile0_node5 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,3] 3 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,3] 3 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 19 13 15 23), lower := (rows 15 19 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) }] }

theorem profile0_node6 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,9] 3 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,9] 3 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 14 13 21), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) }] }

theorem profile0_node7 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,10] 3 profile0_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17,10] 3 profile0_node7_cert).mp (by decide +kernel))

def profile0_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node4 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17] 3 (by decide) (choices 2) [3,9,10] profile0_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,17] (choices 2) [3,9,10] profile0_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7

def profile0_node8_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 22 15 11 27), lower := (rows 15 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile0_node8 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,20] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,20] 3 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14,20] 3 profile0_node8_cert).mp (by decide +kernel))

def profile0_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile0_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [14] (choices 2) [5,12,17,20] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4
  · exact profile0_node8

def profile0_node10_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 7 15 11 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node10 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,5] 3 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,5] 3 profile0_node10_cert).mp (by decide +kernel))

def profile0_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 11 7 13 29), lower := (rows 23 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile0_node12 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,3] 3 profile0_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,3] 3 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 23 11 13 15 23), lower := (rows 23 11 13 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) }] }

theorem profile0_node13 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,9] 3 profile0_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,9] 3 profile0_node13_cert).mp (by decide +kernel))

def profile0_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 11 14 13 21), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) }] }

theorem profile0_node14 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,10] 3 profile0_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9,10] 3 profile0_node14_cert).mp (by decide +kernel))

def profile0_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node11 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9] 3 (by decide) (choices 2) [3,9,10] profile0_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,9] (choices 2) [3,9,10] profile0_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node12
  · exact profile0_node13
  · exact profile0_node14

def profile0_node15_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 14 15 11 27), lower := (rows 23 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile0_node15 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,12] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,12] 3 profile0_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22,12] 3 profile0_node15_cert).mp (by decide +kernel))

def profile0_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node9 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22] 3 (by decide) (choices 2) [5,9,12] profile0_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [22] (choices 2) [5,9,12] profile0_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node10
  · exact profile0_node11
  · exact profile0_node15

def profile0_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [] 3 (by decide) (choices 3) [14,22] profile0_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [] (choices 3) [14,22] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node9

theorem profile0 : Upper (D (n:=5) [51,34,34,34,17]) (R (n:=5) [51,34,34,34,17]) [] 3 := profile0_node0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile1_node2 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,5] 3 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,5] 3 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) }] }

theorem profile1_node3 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,12] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,12] 3 profile1_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,12] 3 profile1_node3_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 19 7 14 30), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile1_node5 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,3] 3 profile1_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,3] 3 profile1_node5_cert).mp (by decide +kernel))

def profile1_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 19 13 14 22), lower := (rows 15 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile1_node6 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,9] 3 profile1_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,9] 3 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 14 15 23), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) }] }

theorem profile1_node7 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,10] 3 profile1_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17,10] 3 profile1_node7_cert).mp (by decide +kernel))

def profile1_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node4 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17] 3 (by decide) (choices 2) [3,9,10] profile1_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,17] (choices 2) [3,9,10] profile1_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node5
  · exact profile1_node6
  · exact profile1_node7

def profile1_node8_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 22 15 11 27), lower := (rows 15 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile1_node8 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,20] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,20] 3 profile1_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14,20] 3 profile1_node8_cert).mp (by decide +kernel))

def profile1_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14] 3 (by decide) (choices 2) [5,12,17,20] profile1_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [14] (choices 2) [5,12,17,20] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node8

def profile1_node10_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 7 15 11 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile1_node10 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,5] 3 profile1_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,5] 3 profile1_node10_cert).mp (by decide +kernel))

def profile1_node12_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 11 7 14 30), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile1_node12 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,3] 3 profile1_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,3] 3 profile1_node12_cert).mp (by decide +kernel))

def profile1_node13_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 11 13 14 22), lower := (rows 23 11 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile1_node13 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,9] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,9] 3 profile1_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,9] 3 profile1_node13_cert).mp (by decide +kernel))

def profile1_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 11 14 15 23), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) }] }

theorem profile1_node14 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,10] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,10] 3 profile1_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9,10] 3 profile1_node14_cert).mp (by decide +kernel))

def profile1_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node11 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9] 3 (by decide) (choices 2) [3,9,10] profile1_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,9] (choices 2) [3,9,10] profile1_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node12
  · exact profile1_node13
  · exact profile1_node14

def profile1_node15_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 14 15 11 27), lower := (rows 23 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile1_node15 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,12] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,12] 3 profile1_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22,12] 3 profile1_node15_cert).mp (by decide +kernel))

def profile1_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node9 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22] 3 (by decide) (choices 2) [5,9,12] profile1_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [22] (choices 2) [5,9,12] profile1_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node10
  · exact profile1_node11
  · exact profile1_node15

def profile1_node17_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 29 7 15 11 27), lower := (rows 29 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile1_node17 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,5] 3 profile1_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,5] 3 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 14 7 11 19), lower := (rows 29 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) }] }

theorem profile1_node18 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,12] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,12] 3 profile1_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28,12] 3 profile1_node18_cert).mp (by decide +kernel))

def profile1_node16_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile1_node16 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28] 3 (by decide) (choices 2) [5,12] profile1_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [28] (choices 2) [5,12] profile1_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node17
  · exact profile1_node18

def profile1_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [] 3 (by decide) (choices 3) [14,22,28] profile1_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [] (choices 3) [14,22,28] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node9
  · exact profile1_node16

theorem profile1 : Upper (D (n:=5) [50,35,34,34,17]) (R (n:=5) [50,35,34,34,17]) [] 3 := profile1_node0

def profile2_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 7 31 27 27), lower := (rows 31 7 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 7 4 0 16) }] }

theorem profile2_node2 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,5] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,5] 3 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,5] 3 profile2_node2_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 11 23 31 23), lower := (rows 31 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) }] }

theorem profile2_node3 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,9] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,9] 3 profile2_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,9] 3 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) }] }

theorem profile2_node4 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,12] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,12] 3 profile2_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,12] 3 profile2_node4_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 26 7 15 23), lower := (rows 31 26 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 26 4 8 16) }] }

theorem profile2_node5 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,24] 3 :=
  cut_bound_sound (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,24] 3 profile2_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30,24] 3 profile2_node5_cert).mp (by decide +kernel))

def profile2_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30] 3 (by decide) (choices 2) [5,9,12,24] profile2_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [30] (choices 2) [5,9,12,24] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node5

def profile2_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [] 3 := by
  apply routed_branch (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [] 3 (by decide) (choices 4) [30] profile2_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [] (choices 4) [30] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [66,34,34,18,18]) (R (n:=5) [66,34,34,18,18]) [] 3 := profile2_node0

def profile3_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile3_node2 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,13] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,13] 3 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,13] 3 profile3_node2_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 23 7 24 24), lower := (rows 15 23 7 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile3_node4 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,3] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,3] 3 profile3_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,3] 3 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 23 13 26 18), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) }] }

theorem profile3_node5 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,9] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,9] 3 profile3_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,9] 3 profile3_node5_cert).mp (by decide +kernel))

def profile3_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 23 14 25 17), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) }] }

theorem profile3_node6 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,10] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,10] 3 profile3_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,10] 3 profile3_node6_cert).mp (by decide +kernel))

def profile3_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 23 21 10 26), lower := (rows 15 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile3_node7 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,17] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,17] 3 profile3_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,17] 3 profile3_node7_cert).mp (by decide +kernel))

def profile3_node8_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 23 22 9 25), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile3_node8 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,18] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,18] 3 profile3_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,18] 3 profile3_node8_cert).mp (by decide +kernel))

def profile3_node9_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 23 28 11 19), lower := (rows 15 23 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile3_node9 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,24] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,24] 3 profile3_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21,24] 3 profile3_node9_cert).mp (by decide +kernel))

def profile3_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node3 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile3_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,21] (choices 2) [3,9,10,17,18,24] profile3_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile3_node4
  · exact profile3_node5
  · exact profile3_node6
  · exact profile3_node7
  · exact profile3_node8
  · exact profile3_node9

def profile3_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 23 31 23), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile3_node10 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,25] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,25] 3 profile3_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,25] 3 profile3_node10_cert).mp (by decide +kernel))

def profile3_node11_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 30 23 27 19), lower := (rows 15 30 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) }] }

theorem profile3_node11 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,28] 3 profile3_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14,28] 3 profile3_node11_cert).mp (by decide +kernel))

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14] 3 (by decide) (choices 3) [13,21,25,28] profile3_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [14] (choices 3) [13,21,25,28] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node3
  · exact profile3_node10
  · exact profile3_node11

def profile3_node13_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 23 31 23), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile3_node13 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,13] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,13] 3 profile3_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,13] 3 profile3_node13_cert).mp (by decide +kernel))

def profile3_node14_cert : CutBound 5 := { lost := (rows 4 4 0 0 0), upper := (rows 27 27 7 15 23), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile3_node14 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,25] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,25] 3 profile3_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,25] 3 profile3_node14_cert).mp (by decide +kernel))

def profile3_node15_cert : CutBound 5 := { lost := (rows 4 0 0 0 0), upper := (rows 27 30 7 15 23), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile3_node15 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,28] 3 profile3_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26,28] 3 profile3_node15_cert).mp (by decide +kernel))

def profile3_node12_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node12 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26] 3 (by decide) (choices 3) [13,25,28] profile3_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [26] (choices 3) [13,25,28] profile3_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node13
  · exact profile3_node14
  · exact profile3_node15

def profile3_node17_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile3_node17 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,13] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,13] 3 profile3_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,13] 3 profile3_node17_cert).mp (by decide +kernel))

def profile3_node18_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 29 27 7 15 23), lower := (rows 29 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile3_node18 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,25] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,25] 3 profile3_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,25] 3 profile3_node18_cert).mp (by decide +kernel))

def profile3_node19_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 29 30 7 11 19), lower := (rows 29 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile3_node19 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,28] 3 :=
  cut_bound_sound (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,28] 3 profile3_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28,28] 3 profile3_node19_cert).mp (by decide +kernel))

def profile3_node16_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node16 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28] 3 (by decide) (choices 3) [13,25,28] profile3_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [28] (choices 3) [13,25,28] profile3_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node17
  · exact profile3_node18
  · exact profile3_node19

def profile3_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [] 3 (by decide) (choices 3) [14,26,28] profile3_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [] (choices 3) [14,26,28] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node12
  · exact profile3_node16

theorem profile3 : Upper (D (n:=5) [50,50,34,18,18]) (R (n:=5) [50,50,34,18,18]) [] 3 := profile3_node0

def profile4_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 15 7 23 27 19), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile4_node2 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,5] 3 profile4_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,5] 3 profile4_node2_cert).mp (by decide +kernel))

def profile4_node4_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 15 19 7 29 21), lower := (rows 15 19 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile4_node4 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,3] 3 profile4_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,3] 3 profile4_node4_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 5 := { lost := (rows 0 4 2 0 0), upper := (rows 15 19 21 15 23), lower := (rows 15 19 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 19 19 8 16) }] }

theorem profile4_node5 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,17] 3 profile4_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,17] 3 profile4_node5_cert).mp (by decide +kernel))

def profile4_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 15 19 22 13 21), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile4_node6 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,18] 3 profile4_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17,18] 3 profile4_node6_cert).mp (by decide +kernel))

def profile4_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node3 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17] 3 (by decide) (choices 2) [3,17,18] profile4_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,17] (choices 2) [3,17,18] profile4_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node4
  · exact profile4_node5
  · exact profile4_node6

def profile4_node8_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 15 22 7 25 17), lower := (rows 15 22 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) }] }

theorem profile4_node8 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,3] 3 profile4_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,3] 3 profile4_node8_cert).mp (by decide +kernel))

def profile4_node9_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 15 22 21 11 19), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) }] }

theorem profile4_node9 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,17] 3 profile4_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20,17] 3 profile4_node9_cert).mp (by decide +kernel))

def profile4_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node7 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20] 3 (by decide) (choices 2) [3,17] profile4_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14,20] (choices 2) [3,17] profile4_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node8
  · exact profile4_node9

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14] 3 (by decide) (choices 2) [5,17,20] profile4_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [14] (choices 2) [5,17,20] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node7

def profile4_node11_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 23 7 31 27 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 7 7 4 8 0) }] }

theorem profile4_node11 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,5] 3 profile4_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,5] 3 profile4_node11_cert).mp (by decide +kernel))

def profile4_node13_cert : CutBound 5 := { lost := (rows 0 0 16 2 0), upper := (rows 23 11 7 29 21), lower := (rows 23 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile4_node13 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,3] 3 profile4_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,3] 3 profile4_node13_cert).mp (by decide +kernel))

def profile4_node14_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 23 11 21 15 23), lower := (rows 23 11 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) },{ target := 4, region := (rows 1 7 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile4_node14 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,17] 3 profile4_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,17] 3 profile4_node14_cert).mp (by decide +kernel))

def profile4_node15_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 23 11 22 13 21), lower := (rows 23 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) }] }

theorem profile4_node15 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,18] 3 profile4_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9,18] 3 profile4_node15_cert).mp (by decide +kernel))

def profile4_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node12 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9] 3 (by decide) (choices 2) [3,17,18] profile4_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,9] (choices 2) [3,17,18] profile4_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node13
  · exact profile4_node14
  · exact profile4_node15

def profile4_node17_cert : CutBound 5 := { lost := (rows 0 0 0 6 0), upper := (rows 23 14 7 25 17), lower := (rows 23 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) }] }

theorem profile4_node17 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,3] 3 profile4_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,3] 3 profile4_node17_cert).mp (by decide +kernel))

def profile4_node18_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 23 14 21 11 19), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) }] }

theorem profile4_node18 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,17] 3 profile4_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12,17] 3 profile4_node18_cert).mp (by decide +kernel))

def profile4_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node16 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12] 3 (by decide) (choices 2) [3,17] profile4_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,12] (choices 2) [3,17] profile4_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node17
  · exact profile4_node18

def profile4_node19_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 23 19 15 15 31), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile4_node19 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,17] 3 profile4_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,17] 3 profile4_node19_cert).mp (by decide +kernel))

def profile4_node20_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 23 22 15 11 27), lower := (rows 23 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 22 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile4_node20 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,20] 3 profile4_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,20] 3 profile4_node20_cert).mp (by decide +kernel))

def profile4_node21_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 26 7 15 23), lower := (rows 23 26 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile4_node21 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,24] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,24] 3 profile4_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22,24] 3 profile4_node21_cert).mp (by decide +kernel))

def profile4_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node10 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile4_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [22] (choices 2) [5,9,12,17,20,24] profile4_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node11
  · exact profile4_node12
  · exact profile4_node16
  · exact profile4_node19
  · exact profile4_node20
  · exact profile4_node21

def profile4_node24_cert : CutBound 5 := { lost := (rows 0 16 16 2 0), upper := (rows 27 7 7 29 21), lower := (rows 27 7 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile4_node24 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,3] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,3] 3 profile4_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,3] 3 profile4_node24_cert).mp (by decide +kernel))

def profile4_node25_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 27 7 21 15 23), lower := (rows 27 7 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 21 8 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile4_node25 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,17] 3 profile4_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,17] 3 profile4_node25_cert).mp (by decide +kernel))

def profile4_node26_cert : CutBound 5 := { lost := (rows 0 0 1 2 0), upper := (rows 27 7 22 13 21), lower := (rows 27 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 22 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) }] }

theorem profile4_node26 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,18] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,18] 3 profile4_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5,18] 3 profile4_node26_cert).mp (by decide +kernel))

def profile4_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node23 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5] 3 (by decide) (choices 2) [3,17,18] profile4_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,5] (choices 2) [3,17,18] profile4_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node24
  · exact profile4_node25
  · exact profile4_node26

def profile4_node27_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 27 19 7 15 23), lower := (rows 27 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile4_node27 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,17] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,17] 3 profile4_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,17] 3 profile4_node27_cert).mp (by decide +kernel))

def profile4_node28_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 22 7 15 23), lower := (rows 27 22 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile4_node28 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,20] 3 :=
  cut_bound_sound (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,20] 3 profile4_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26,20] 3 profile4_node28_cert).mp (by decide +kernel))

def profile4_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node22 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26] 3 (by decide) (choices 2) [5,17,20] profile4_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [26] (choices 2) [5,17,20] profile4_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node23
  · exact profile4_node27
  · exact profile4_node28

def profile4_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [] 3 (by decide) (choices 3) [14,22,26] profile4_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [] (choices 3) [14,22,26] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node10
  · exact profile4_node22

theorem profile4 : Upper (D (n:=5) [51,34,34,33,18]) (R (n:=5) [51,34,34,33,18]) [] 3 := profile4_node0

def profile5_node2_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 15 7 23 27 19), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile5_node2 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,5] 3 profile5_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,5] 3 profile5_node2_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 5 := { lost := (rows 0 0 16 1 0), upper := (rows 15 19 7 30 22), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile5_node4 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,3] 3 profile5_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,3] 3 profile5_node4_cert).mp (by decide +kernel))

def profile5_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 15 19 21 14 22), lower := (rows 15 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) }] }

theorem profile5_node5 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,17] 3 profile5_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,17] 3 profile5_node5_cert).mp (by decide +kernel))

def profile5_node6_cert : CutBound 5 := { lost := (rows 16 0 1 16 0), upper := (rows 15 19 22 15 23), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile5_node6 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,18] 3 profile5_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17,18] 3 profile5_node6_cert).mp (by decide +kernel))

def profile5_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node3 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17] 3 (by decide) (choices 2) [3,17,18] profile5_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,17] (choices 2) [3,17,18] profile5_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node4
  · exact profile5_node5
  · exact profile5_node6

def profile5_node8_cert : CutBound 5 := { lost := (rows 0 0 16 4 0), upper := (rows 15 22 7 27 19), lower := (rows 15 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 6 7 8 0) }] }

theorem profile5_node8 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,3] 3 profile5_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,3] 3 profile5_node8_cert).mp (by decide +kernel))

def profile5_node9_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 15 22 21 11 19), lower := (rows 15 22 21 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 25 8 16) }] }

theorem profile5_node9 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,17] 3 profile5_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,17] 3 profile5_node9_cert).mp (by decide +kernel))

def profile5_node10_cert : CutBound 5 := { lost := (rows 0 1 1 0 0), upper := (rows 15 22 22 11 19), lower := (rows 15 22 22 8 16), losses := [{ target := 0, region := (rows 0 22 22 8 16), good := (rows 14 22 22 8 22) }] }

theorem profile5_node10 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,18] 3 profile5_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20,18] 3 profile5_node10_cert).mp (by decide +kernel))

def profile5_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node7 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20] 3 (by decide) (choices 2) [3,17,18] profile5_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14,20] (choices 2) [3,17,18] profile5_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node8
  · exact profile5_node9
  · exact profile5_node10

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14] 3 (by decide) (choices 2) [5,17,20] profile5_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [14] (choices 2) [5,17,20] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node7

def profile5_node12_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 23 7 31 27 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 7 7 4 8 0) }] }

theorem profile5_node12 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,5] 3 profile5_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,5] 3 profile5_node12_cert).mp (by decide +kernel))

def profile5_node14_cert : CutBound 5 := { lost := (rows 0 0 16 1 0), upper := (rows 23 11 7 30 22), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 7 15 7 8 0) }] }

theorem profile5_node14 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,3] 3 profile5_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,3] 3 profile5_node14_cert).mp (by decide +kernel))

def profile5_node15_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 23 11 21 14 22), lower := (rows 23 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 13 21 8 16) }] }

theorem profile5_node15 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,17] 3 profile5_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,17] 3 profile5_node15_cert).mp (by decide +kernel))

def profile5_node16_cert : CutBound 5 := { lost := (rows 0 16 1 16 0), upper := (rows 23 11 22 15 23), lower := (rows 23 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 11 6 8 0) }] }

theorem profile5_node16 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,18] 3 profile5_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9,18] 3 profile5_node16_cert).mp (by decide +kernel))

def profile5_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node13 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9] 3 (by decide) (choices 2) [3,17,18] profile5_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,9] (choices 2) [3,17,18] profile5_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node14
  · exact profile5_node15
  · exact profile5_node16

def profile5_node18_cert : CutBound 5 := { lost := (rows 0 0 16 4 0), upper := (rows 23 14 7 27 19), lower := (rows 23 14 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 7 14 7 8 0) }] }

theorem profile5_node18 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,3] 3 profile5_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,3] 3 profile5_node18_cert).mp (by decide +kernel))

def profile5_node19_cert : CutBound 5 := { lost := (rows 0 0 2 4 0), upper := (rows 23 14 21 11 19), lower := (rows 23 14 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 21 12 21 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) }] }

theorem profile5_node19 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,17] 3 profile5_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,17] 3 profile5_node19_cert).mp (by decide +kernel))

def profile5_node20_cert : CutBound 5 := { lost := (rows 0 0 1 4 0), upper := (rows 23 14 22 11 19), lower := (rows 23 14 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 18 8 16) }] }

theorem profile5_node20 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,18] 3 profile5_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12,18] 3 profile5_node20_cert).mp (by decide +kernel))

def profile5_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node17 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12] 3 (by decide) (choices 2) [3,17,18] profile5_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,12] (choices 2) [3,17,18] profile5_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node18
  · exact profile5_node19
  · exact profile5_node20

def profile5_node21_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 23 19 15 15 31), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile5_node21 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,17] 3 profile5_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,17] 3 profile5_node21_cert).mp (by decide +kernel))

def profile5_node22_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 23 22 15 11 27), lower := (rows 23 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 22 22 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile5_node22 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,20] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,20] 3 profile5_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,20] 3 profile5_node22_cert).mp (by decide +kernel))

def profile5_node23_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 26 7 15 23), lower := (rows 23 26 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile5_node23 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,24] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,24] 3 profile5_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22,24] 3 profile5_node23_cert).mp (by decide +kernel))

def profile5_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node11 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile5_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [22] (choices 2) [5,9,12,17,20,24] profile5_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node12
  · exact profile5_node13
  · exact profile5_node17
  · exact profile5_node21
  · exact profile5_node22
  · exact profile5_node23

def profile5_node26_cert : CutBound 5 := { lost := (rows 0 16 16 1 0), upper := (rows 27 7 7 30 22), lower := (rows 27 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile5_node26 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,3] 3 profile5_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,3] 3 profile5_node26_cert).mp (by decide +kernel))

def profile5_node27_cert : CutBound 5 := { lost := (rows 0 0 2 1 0), upper := (rows 27 7 21 14 22), lower := (rows 27 7 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 20 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 21 8 16) }] }

theorem profile5_node27 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,17] 3 profile5_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,17] 3 profile5_node27_cert).mp (by decide +kernel))

def profile5_node28_cert : CutBound 5 := { lost := (rows 0 0 1 16 0), upper := (rows 27 7 22 15 23), lower := (rows 27 7 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 22 8 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 14 8 0) }] }

theorem profile5_node28 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,18] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,18] 3 profile5_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5,18] 3 profile5_node28_cert).mp (by decide +kernel))

def profile5_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node25 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5] 3 (by decide) (choices 2) [3,17,18] profile5_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,5] (choices 2) [3,17,18] profile5_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node26
  · exact profile5_node27
  · exact profile5_node28

def profile5_node29_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 27 19 7 15 23), lower := (rows 27 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile5_node29 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,17] 3 profile5_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,17] 3 profile5_node29_cert).mp (by decide +kernel))

def profile5_node30_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 22 7 15 23), lower := (rows 27 22 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 6 4 8 0) }] }

theorem profile5_node30 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,20] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,20] 3 profile5_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26,20] 3 profile5_node30_cert).mp (by decide +kernel))

def profile5_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node24 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26] 3 (by decide) (choices 2) [5,17,20] profile5_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [26] (choices 2) [5,17,20] profile5_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node25
  · exact profile5_node29
  · exact profile5_node30

def profile5_node32_cert : CutBound 5 := { lost := (rows 0 16 0 4 0), upper := (rows 29 7 23 27 19), lower := (rows 29 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 7 4 8 0) }] }

theorem profile5_node32 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,5] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,5] 3 profile5_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,5] 3 profile5_node32_cert).mp (by decide +kernel))

def profile5_node33_cert : CutBound 5 := { lost := (rows 0 4 16 16 0), upper := (rows 29 19 7 15 23), lower := (rows 29 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 19 0 8 16) },{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile5_node33 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,17] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,17] 3 profile5_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,17] 3 profile5_node33_cert).mp (by decide +kernel))

def profile5_node35_cert : CutBound 5 := { lost := (rows 0 1 0 4 0), upper := (rows 29 22 7 11 19), lower := (rows 29 22 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 22 6 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile5_node35 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20,3] 3 :=
  cut_bound_sound (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20,3] 3 profile5_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20,3] 3 profile5_node35_cert).mp (by decide +kernel))

def profile5_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node34 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20] 3 (by decide) (choices 2) [3] profile5_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28,20] (choices 2) [3] profile5_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node35

def profile5_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node31 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28] 3 (by decide) (choices 2) [5,17,20] profile5_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [28] (choices 2) [5,17,20] profile5_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile5_node32
  · exact profile5_node33
  · exact profile5_node34

def profile5_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [] 3 := by
  apply routed_branch (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [] 3 (by decide) (choices 3) [14,22,26,28] profile5_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [] (choices 3) [14,22,26,28] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node1
  · exact profile5_node11
  · exact profile5_node24
  · exact profile5_node31

theorem profile5 : Upper (D (n:=5) [50,35,34,33,18]) (R (n:=5) [50,35,34,33,18]) [] 3 := profile5_node0

#print axioms profile5
end Delivery.FiveVertexPositive10
