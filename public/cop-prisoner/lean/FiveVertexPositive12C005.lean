import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile77_node3_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 31 7 13 14 30), lower := (rows 31 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) }] }

theorem profile77_node3 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,9] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,9] 2 profile77_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,9] 2 profile77_node3_cert).mp (by decide +kernel))

def profile77_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 3), upper := (rows 31 7 14 11 28), lower := (rows 31 7 14 11 16), losses := [{ target := 0, region := (rows 0 2 13 8 29), good := (rows 30 22 30 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 28 25 16) }] }

theorem profile77_node5 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,3] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,3] 2 profile77_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,3] 2 profile77_node5_cert).mp (by decide +kernel))

def profile77_node6_cert : CutBound 5 := { lost := (rows 0 0 1 2 1), upper := (rows 31 7 14 13 26), lower := (rows 31 7 14 13 16), losses := [{ target := 0, region := (rows 0 2 5 8 21), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 12 13 16) }] }

theorem profile77_node6 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,5] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,5] 2 profile77_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,5] 2 profile77_node6_cert).mp (by decide +kernel))

def profile77_node7_cert : CutBound 5 := { lost := (rows 0 0 1 1 2), upper := (rows 31 7 14 14 25), lower := (rows 31 7 14 14 16), losses := [{ target := 0, region := (rows 0 2 15 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 12 12 16) }] }

theorem profile77_node7 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,6] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,6] 2 profile77_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10,6] 2 profile77_node7_cert).mp (by decide +kernel))

def profile77_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node4 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10] 2 (by decide) (choices 2) [3,5,6] profile77_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5,10] (choices 2) [3,5,6] profile77_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node5
  · exact profile77_node6
  · exact profile77_node7

def profile77_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node2 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5] 2 (by decide) (choices 2) [9,10] profile77_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,5] (choices 2) [9,10] profile77_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node3
  · exact profile77_node4

def profile77_node10_cert : CutBound 5 := { lost := (rows 0 1 0 0 3), upper := (rows 31 14 7 11 28), lower := (rows 31 14 7 11 16), losses := [{ target := 0, region := (rows 0 3 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 28 21 25 16) }] }

theorem profile77_node10 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,3] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,3] 2 profile77_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,3] 2 profile77_node10_cert).mp (by decide +kernel))

def profile77_node11_cert : CutBound 5 := { lost := (rows 0 1 0 2 1), upper := (rows 31 14 7 13 26), lower := (rows 31 14 7 13 16), losses := [{ target := 0, region := (rows 0 11 4 8 27), good := (rows 30 30 22 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 12 13 13 16) }] }

theorem profile77_node11 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,5] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,5] 2 profile77_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,5] 2 profile77_node11_cert).mp (by decide +kernel))

def profile77_node12_cert : CutBound 5 := { lost := (rows 0 1 0 1 2), upper := (rows 31 14 7 14 25), lower := (rows 31 14 7 14 16), losses := [{ target := 0, region := (rows 0 15 4 15 16), good := (rows 30 14 14 14 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 12 21 12 16) }] }

theorem profile77_node12 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,6] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,6] 2 profile77_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3,6] 2 profile77_node12_cert).mp (by decide +kernel))

def profile77_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node9 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3] 2 (by decide) (choices 2) [3,5,6] profile77_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,3] (choices 2) [3,5,6] profile77_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node10
  · exact profile77_node11
  · exact profile77_node12

def profile77_node13_cert : CutBound 5 := { lost := (rows 0 1 2 0 8), upper := (rows 31 14 13 15 23), lower := (rows 31 14 13 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 13 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 6 21 0 16) }] }

theorem profile77_node13 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,9] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,9] 2 profile77_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,9] 2 profile77_node13_cert).mp (by decide +kernel))

def profile77_node14_cert : CutBound 5 := { lost := (rows 0 1 1 0 8), upper := (rows 31 14 14 15 23), lower := (rows 31 14 14 8 16), losses := [{ target := 0, region := (rows 0 15 15 8 16), good := (rows 30 14 14 14 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 6 6 0 16) }] }

theorem profile77_node14 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,10] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,10] 2 profile77_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12,10] 2 profile77_node14_cert).mp (by decide +kernel))

def profile77_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node8 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12] 2 (by decide) (choices 2) [3,9,10] profile77_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30,12] (choices 2) [3,9,10] profile77_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node9
  · exact profile77_node13
  · exact profile77_node14

def profile77_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile77_node1 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30] 2 (by decide) (choices 2) [5,12] profile77_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [30] (choices 2) [5,12] profile77_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile77_node2
  · exact profile77_node8

def profile77_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node0 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [] 2 (by decide) (choices 4) [30] profile77_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [] (choices 4) [30] profile77_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node1

theorem profile77 : Upper (D (n:=5) [66,35,35,35,33]) (R (n:=5) [66,35,35,35,33]) [] 2 := profile77_node0

def profile78_node3_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 15 7 29 29), lower := (rows 15 15 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile78_node3 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,3] 2 profile78_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,3] 2 profile78_node3_cert).mp (by decide +kernel))

def profile78_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 9), upper := (rows 15 15 13 25 22), lower := (rows 15 15 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 24 16) },{ target := 1, region := (rows 1 0 15 8 16), good := (rows 13 13 13 29 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 17 16) }] }

theorem profile78_node5 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,17] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,17] 2 profile78_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,17] 2 profile78_node5_cert).mp (by decide +kernel))

def profile78_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 10), upper := (rows 15 15 13 26 21), lower := (rows 15 15 13 26 16), losses := [{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 18 16) }] }

theorem profile78_node6 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,18] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,18] 2 profile78_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,18] 2 profile78_node6_cert).mp (by decide +kernel))

def profile78_node7_cert : CutBound 5 := { lost := (rows 0 0 2 0 12), upper := (rows 15 15 13 28 19), lower := (rows 15 15 13 28 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 13 13 13 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 25 24 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 20 16) }] }

theorem profile78_node7 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,20] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,20] 2 profile78_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9,20] 2 profile78_node7_cert).mp (by decide +kernel))

def profile78_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node4 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9] 2 (by decide) (choices 2) [17,18,20] profile78_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,9] (choices 2) [17,18,20] profile78_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node5
  · exact profile78_node6
  · exact profile78_node7

def profile78_node8_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 15 14 29 21), lower := (rows 15 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 14 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile78_node8 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,10] 2 profile78_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,10] 2 profile78_node8_cert).mp (by decide +kernel))

def profile78_node10_cert : CutBound 5 := { lost := (rows 0 0 2 0 3), upper := (rows 15 15 21 11 28), lower := (rows 15 15 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 26 16) },{ target := 1, region := (rows 1 0 15 8 27), good := (rows 29 29 21 29 16) }] }

theorem profile78_node10 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,3] 2 profile78_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,3] 2 profile78_node10_cert).mp (by decide +kernel))

def profile78_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 15 15 21 13 26), lower := (rows 15 15 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 20 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 13 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 17 25 16) }] }

theorem profile78_node11 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,5] 2 profile78_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,5] 2 profile78_node11_cert).mp (by decide +kernel))

def profile78_node12_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 15 21 14 25), lower := (rows 15 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 1, region := (rows 1 0 7 8 19), good := (rows 29 29 21 28 16) }] }

theorem profile78_node12 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,6] 2 profile78_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17,6] 2 profile78_node12_cert).mp (by decide +kernel))

def profile78_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node9 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17] 2 (by decide) (choices 2) [3,5,6] profile78_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,17] (choices 2) [3,5,6] profile78_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node10
  · exact profile78_node11
  · exact profile78_node12

def profile78_node14_cert : CutBound 5 := { lost := (rows 0 0 0 2 6), upper := (rows 15 15 22 13 25), lower := (rows 15 15 22 13 16), losses := [{ target := 1, region := (rows 1 0 4 11 27), good := (rows 29 29 28 29 16) },{ target := 2, region := (rows 1 2 0 8 27), good := (rows 27 27 18 25 16) }] }

theorem profile78_node14 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18,5] 2 profile78_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18,5] 2 profile78_node14_cert).mp (by decide +kernel))

def profile78_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node13 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18] 2 (by decide) (choices 2) [5] profile78_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,18] (choices 2) [5] profile78_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node14

def profile78_node16_cert : CutBound 5 := { lost := (rows 0 0 2 4 2), upper := (rows 15 15 28 11 21), lower := (rows 15 15 28 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 27), good := (rows 29 29 28 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 11 24 11 16) }] }

theorem profile78_node16 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,3] 2 profile78_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,3] 2 profile78_node16_cert).mp (by decide +kernel))

def profile78_node17_cert : CutBound 5 := { lost := (rows 0 0 0 2 12), upper := (rows 15 15 28 13 19), lower := (rows 15 15 28 13 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 24 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 21 16) }] }

theorem profile78_node17 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,5] 2 profile78_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24,5] 2 profile78_node17_cert).mp (by decide +kernel))

def profile78_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node15 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24] 2 (by decide) (choices 2) [3,5] profile78_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13,24] (choices 2) [3,5] profile78_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node16
  · exact profile78_node17

def profile78_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node2 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile78_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,13] (choices 2) [3,9,10,17,18,24] profile78_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile78_node3
  · exact profile78_node4
  · exact profile78_node8
  · exact profile78_node9
  · exact profile78_node13
  · exact profile78_node15

def profile78_node20_cert : CutBound 5 := { lost := (rows 0 0 2 0 3), upper := (rows 15 23 13 11 28), lower := (rows 15 23 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 28 26 16) },{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 21 29 29 16) }] }

theorem profile78_node20 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,3] 2 profile78_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,3] 2 profile78_node20_cert).mp (by decide +kernel))

def profile78_node21_cert : CutBound 5 := { lost := (rows 0 0 2 2 1), upper := (rows 15 23 13 13 26), lower := (rows 15 23 13 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 28 28 16) },{ target := 1, region := (rows 1 0 15 15 16), good := (rows 13 29 13 13 16) }] }

theorem profile78_node21 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,5] 2 profile78_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,5] 2 profile78_node21_cert).mp (by decide +kernel))

def profile78_node22_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 23 13 14 25), lower := (rows 15 23 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 30 12 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 21 29 28 16) }] }

theorem profile78_node22 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,6] 2 profile78_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9,6] 2 profile78_node22_cert).mp (by decide +kernel))

def profile78_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node19 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9] 2 (by decide) (choices 2) [3,5,6] profile78_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,9] (choices 2) [3,5,6] profile78_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node20
  · exact profile78_node21
  · exact profile78_node22

def profile78_node23_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 23 14 13 29), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile78_node23 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,10] 2 profile78_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21,10] 2 profile78_node23_cert).mp (by decide +kernel))

def profile78_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node18 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21] 2 (by decide) (choices 2) [9,10] profile78_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,21] (choices 2) [9,10] profile78_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node19
  · exact profile78_node23

def profile78_node25_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 30 7 13 29), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile78_node25 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,3] 2 profile78_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,3] 2 profile78_node25_cert).mp (by decide +kernel))

def profile78_node27_cert : CutBound 5 := { lost := (rows 0 0 2 4 2), upper := (rows 15 30 13 11 21), lower := (rows 15 30 13 11 16), losses := [{ target := 1, region := (rows 1 0 13 8 29), good := (rows 29 28 29 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 11 26 9 11 16) }] }

theorem profile78_node27 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,3] 2 profile78_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,3] 2 profile78_node27_cert).mp (by decide +kernel))

def profile78_node28_cert : CutBound 5 := { lost := (rows 0 0 2 2 4), upper := (rows 15 30 13 13 19), lower := (rows 15 30 13 13 16), losses := [{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 26 25 25 16) }] }

theorem profile78_node28 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,5] 2 profile78_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9,5] 2 profile78_node28_cert).mp (by decide +kernel))

def profile78_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node26 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9] 2 (by decide) (choices 2) [3,5] profile78_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28,9] (choices 2) [3,5] profile78_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node27
  · exact profile78_node28

def profile78_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node24 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28] 2 (by decide) (choices 2) [3,9] profile78_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14,28] (choices 2) [3,9] profile78_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node25
  · exact profile78_node26

def profile78_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile78_node1 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14] 2 (by decide) (choices 3) [13,21,28] profile78_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [14] (choices 3) [13,21,28] profile78_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node2
  · exact profile78_node18
  · exact profile78_node24

def profile78_node32_cert : CutBound 5 := { lost := (rows 0 0 2 0 3), upper := (rows 23 15 13 11 28), lower := (rows 23 15 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 28 26 16) },{ target := 1, region := (rows 1 0 14 8 30), good := (rows 21 29 29 29 16) }] }

theorem profile78_node32 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,3] 2 profile78_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,3] 2 profile78_node32_cert).mp (by decide +kernel))

def profile78_node33_cert : CutBound 5 := { lost := (rows 0 0 2 2 1), upper := (rows 23 15 13 13 26), lower := (rows 23 15 13 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 12 12 16) },{ target := 1, region := (rows 1 0 15 15 16), good := (rows 29 13 13 13 16) }] }

theorem profile78_node33 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,5] 2 profile78_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,5] 2 profile78_node33_cert).mp (by decide +kernel))

def profile78_node34_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 23 15 13 14 25), lower := (rows 23 15 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 14 12 14 16) },{ target := 1, region := (rows 1 0 6 8 22), good := (rows 21 29 29 28 16) }] }

theorem profile78_node34 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,6] 2 profile78_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9,6] 2 profile78_node34_cert).mp (by decide +kernel))

def profile78_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node31 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9] 2 (by decide) (choices 2) [3,5,6] profile78_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,9] (choices 2) [3,5,6] profile78_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node32
  · exact profile78_node33
  · exact profile78_node34

def profile78_node35_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 23 15 14 13 29), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile78_node35 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,10] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,10] 2 profile78_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13,10] 2 profile78_node35_cert).mp (by decide +kernel))

def profile78_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node30 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13] 2 (by decide) (choices 2) [9,10] profile78_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22,13] (choices 2) [9,10] profile78_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node31
  · exact profile78_node35

def profile78_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node29 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22] 2 (by decide) (choices 3) [13] profile78_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [22] (choices 3) [13] profile78_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node30

def profile78_node39_cert : CutBound 5 := { lost := (rows 2 0 0 0 3), upper := (rows 29 15 7 11 28), lower := (rows 29 15 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 28 30 22 26 16) },{ target := 1, region := (rows 3 0 4 8 19), good := (rows 29 29 21 25 16) }] }

theorem profile78_node39 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,3] 2 profile78_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,3] 2 profile78_node39_cert).mp (by decide +kernel))

def profile78_node40_cert : CutBound 5 := { lost := (rows 0 0 0 2 5), upper := (rows 29 15 7 13 26), lower := (rows 29 15 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 28 30 22 12 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 13 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 19 9 16) }] }

theorem profile78_node40 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,5] 2 profile78_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,5] 2 profile78_node40_cert).mp (by decide +kernel))

def profile78_node41_cert : CutBound 5 := { lost := (rows 2 0 0 1 2), upper := (rows 29 15 7 14 25), lower := (rows 29 15 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 28 14 14 14 16) },{ target := 1, region := (rows 11 0 4 8 27), good := (rows 29 29 21 29 16) }] }

theorem profile78_node41 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,6] 2 profile78_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3,6] 2 profile78_node41_cert).mp (by decide +kernel))

def profile78_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node38 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3] 2 (by decide) (choices 2) [3,5,6] profile78_node38_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,3] (choices 2) [3,5,6] profile78_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node39
  · exact profile78_node40
  · exact profile78_node41

def profile78_node43_cert : CutBound 5 := { lost := (rows 0 0 2 4 1), upper := (rows 29 15 13 11 22), lower := (rows 29 15 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 28 30 12 26 16) },{ target := 1, region := (rows 1 0 15 8 16), good := (rows 29 13 13 13 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 25 11 9 11 16) }] }

theorem profile78_node43 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,3] 2 profile78_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,3] 2 profile78_node43_cert).mp (by decide +kernel))

def profile78_node44_cert : CutBound 5 := { lost := (rows 0 0 2 1 4), upper := (rows 29 15 13 14 19), lower := (rows 29 15 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 28 14 12 14 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 12 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 9 26 16) }] }

theorem profile78_node44 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,6] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,6] 2 profile78_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9,6] 2 profile78_node44_cert).mp (by decide +kernel))

def profile78_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node42 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9] 2 (by decide) (choices 2) [3,6] profile78_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,9] (choices 2) [3,6] profile78_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node43
  · exact profile78_node44

def profile78_node46_cert : CutBound 5 := { lost := (rows 2 0 1 0 2), upper := (rows 29 15 14 11 21), lower := (rows 29 15 14 11 16), losses := [{ target := 0, region := (rows 0 2 14 8 16), good := (rows 28 14 14 14 16) },{ target := 1, region := (rows 7 0 4 8 23), good := (rows 29 29 29 25 16) }] }

theorem profile78_node46 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,3] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,3] 2 profile78_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,3] 2 profile78_node46_cert).mp (by decide +kernel))

def profile78_node47_cert : CutBound 5 := { lost := (rows 0 0 1 2 4), upper := (rows 29 15 14 13 19), lower := (rows 29 15 14 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 28 14 14 12 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 12 13 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 25 27 26 9 16) }] }

theorem profile78_node47 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,5] 2 :=
  cut_bound_sound (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,5] 2 profile78_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10,5] 2 profile78_node47_cert).mp (by decide +kernel))

def profile78_node45_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node45 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10] 2 (by decide) (choices 2) [3,5] profile78_node45_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13,10] (choices 2) [3,5] profile78_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile78_node46
  · exact profile78_node47

def profile78_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node37 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13] 2 (by decide) (choices 2) [3,9,10] profile78_node37_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28,13] (choices 2) [3,9,10] profile78_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node38
  · exact profile78_node42
  · exact profile78_node45

def profile78_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node36 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28] 2 (by decide) (choices 3) [13] profile78_node36_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [28] (choices 3) [13] profile78_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node37

def profile78_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile78_node0 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [] 2 (by decide) (choices 3) [14,22,28] profile78_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [] (choices 3) [14,22,28] profile78_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node1
  · exact profile78_node29
  · exact profile78_node36

theorem profile78 : Upper (D (n:=5) [51,50,35,35,33]) (R (n:=5) [51,50,35,35,33]) [] 2 := profile78_node0

def profile79_node3_cert : CutBound 5 := { lost := (rows 0 0 0 3 3), upper := (rows 15 15 7 28 28), lower := (rows 15 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile79_node3 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,3] 2 profile79_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,3] 2 profile79_node3_cert).mp (by decide +kernel))

def profile79_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 15 15 13 30 22), lower := (rows 15 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 13 13 13 8 16) }] }

theorem profile79_node4 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,9] 2 profile79_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,9] 2 profile79_node4_cert).mp (by decide +kernel))

def profile79_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 15 14 29 21), lower := (rows 15 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 14 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile79_node5 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,10] 2 profile79_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,10] 2 profile79_node5_cert).mp (by decide +kernel))

def profile79_node7_cert : CutBound 5 := { lost := (rows 0 0 2 1 3), upper := (rows 15 15 21 14 28), lower := (rows 15 15 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 31), good := (rows 30 30 28 30 16) },{ target := 1, region := (rows 1 0 7 8 27), good := (rows 29 29 21 28 16) }] }

theorem profile79_node7 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17,6] 2 profile79_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17,6] 2 profile79_node7_cert).mp (by decide +kernel))

def profile79_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node6 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17] 2 (by decide) (choices 2) [6] profile79_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,17] (choices 2) [6] profile79_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node7

def profile79_node9_cert : CutBound 5 := { lost := (rows 0 0 1 2 3), upper := (rows 15 15 22 13 28), lower := (rows 15 15 22 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 27), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 11 31), good := (rows 29 29 28 29 16) }] }

theorem profile79_node9 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18,5] 2 profile79_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18,5] 2 profile79_node9_cert).mp (by decide +kernel))

def profile79_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node8 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18] 2 (by decide) (choices 2) [5] profile79_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,18] (choices 2) [5] profile79_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node9

def profile79_node11_cert : CutBound 5 := { lost := (rows 0 0 1 2 1), upper := (rows 15 15 28 13 22), lower := (rows 15 15 28 13 16), losses := [{ target := 0, region := (rows 0 2 15 8 19), good := (rows 30 30 28 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 13 13 28 13 16) }] }

theorem profile79_node11 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,5] 2 profile79_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,5] 2 profile79_node11_cert).mp (by decide +kernel))

def profile79_node12_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 15 28 14 21), lower := (rows 15 15 28 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 14 28 14 16) },{ target := 1, region := (rows 1 0 15 8 19), good := (rows 29 29 28 28 16) }] }

theorem profile79_node12 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,6] 2 profile79_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24,6] 2 profile79_node12_cert).mp (by decide +kernel))

def profile79_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node10 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24] 2 (by decide) (choices 2) [5,6] profile79_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13,24] (choices 2) [5,6] profile79_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node11
  · exact profile79_node12

def profile79_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node2 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile79_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,13] (choices 2) [3,9,10,17,18,24] profile79_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile79_node3
  · exact profile79_node4
  · exact profile79_node5
  · exact profile79_node6
  · exact profile79_node8
  · exact profile79_node10

def profile79_node14_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 15 23 13 14 30), lower := (rows 15 23 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) }] }

theorem profile79_node14 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,9] 2 profile79_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,9] 2 profile79_node14_cert).mp (by decide +kernel))

def profile79_node15_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 23 14 13 29), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile79_node15 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,10] 2 profile79_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21,10] 2 profile79_node15_cert).mp (by decide +kernel))

def profile79_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node13 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21] 2 (by decide) (choices 2) [9,10] profile79_node13_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,21] (choices 2) [9,10] profile79_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node14
  · exact profile79_node15

def profile79_node17_cert : CutBound 5 := { lost := (rows 0 0 8 2 2), upper := (rows 15 30 7 13 29), lower := (rows 15 30 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 7 22 7 0 16) }] }

theorem profile79_node17 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,3] 2 profile79_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,3] 2 profile79_node17_cert).mp (by decide +kernel))

def profile79_node19_cert : CutBound 5 := { lost := (rows 0 1 2 2 1), upper := (rows 15 30 13 13 22), lower := (rows 15 30 13 13 16), losses := [{ target := 0, region := (rows 0 15 4 8 31), good := (rows 30 30 30 30 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 28 13 13 16) }] }

theorem profile79_node19 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,5] 2 profile79_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,5] 2 profile79_node19_cert).mp (by decide +kernel))

def profile79_node20_cert : CutBound 5 := { lost := (rows 0 0 2 1 2), upper := (rows 15 30 13 14 21), lower := (rows 15 30 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 14 30 12 14 16) },{ target := 1, region := (rows 1 0 5 8 21), good := (rows 29 28 29 28 16) }] }

theorem profile79_node20 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,6] 2 profile79_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9,6] 2 profile79_node20_cert).mp (by decide +kernel))

def profile79_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node18 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9] 2 (by decide) (choices 2) [5,6] profile79_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,9] (choices 2) [5,6] profile79_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node19
  · exact profile79_node20

def profile79_node21_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 15 30 14 13 21), lower := (rows 15 30 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 14 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 12 8 16) }] }

theorem profile79_node21 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,10] 2 profile79_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28,10] 2 profile79_node21_cert).mp (by decide +kernel))

def profile79_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node16 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28] 2 (by decide) (choices 2) [3,9,10] profile79_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14,28] (choices 2) [3,9,10] profile79_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile79_node17
  · exact profile79_node18
  · exact profile79_node21

def profile79_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node1 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14] 2 (by decide) (choices 3) [13,21,28] profile79_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [14] (choices 3) [13,21,28] profile79_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile79_node2
  · exact profile79_node13
  · exact profile79_node16

def profile79_node24_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 23 15 13 14 30), lower := (rows 23 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 13 13 8 16) }] }

theorem profile79_node24 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,9] 2 profile79_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,9] 2 profile79_node24_cert).mp (by decide +kernel))

def profile79_node25_cert : CutBound 5 := { lost := (rows 0 0 1 2 2), upper := (rows 23 15 14 13 29), lower := (rows 23 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) }] }

theorem profile79_node25 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,10] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,10] 2 profile79_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13,10] 2 profile79_node25_cert).mp (by decide +kernel))

def profile79_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node23 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13] 2 (by decide) (choices 2) [9,10] profile79_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22,13] (choices 2) [9,10] profile79_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node24
  · exact profile79_node25

def profile79_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node22 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22] 2 (by decide) (choices 3) [13] profile79_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [22] (choices 3) [13] profile79_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node23

def profile79_node28_cert : CutBound 5 := { lost := (rows 0 0 8 1 1), upper := (rows 29 15 7 14 30), lower := (rows 29 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 28 30 30 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 21 7 7 0 16) }] }

theorem profile79_node28 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,3] 2 profile79_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,3] 2 profile79_node28_cert).mp (by decide +kernel))

def profile79_node29_cert : CutBound 5 := { lost := (rows 0 0 2 1 1), upper := (rows 29 15 13 14 22), lower := (rows 29 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 28 30 12 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) }] }

theorem profile79_node29 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,9] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,9] 2 profile79_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,9] 2 profile79_node29_cert).mp (by decide +kernel))

def profile79_node31_cert : CutBound 5 := { lost := (rows 0 0 1 2 1), upper := (rows 29 15 14 13 22), lower := (rows 29 15 14 13 16), losses := [{ target := 0, region := (rows 0 2 6 8 22), good := (rows 28 30 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 12 13 16) }] }

theorem profile79_node31 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,5] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,5] 2 profile79_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,5] 2 profile79_node31_cert).mp (by decide +kernel))

def profile79_node32_cert : CutBound 5 := { lost := (rows 2 0 1 1 2), upper := (rows 29 15 14 14 21), lower := (rows 29 15 14 14 16), losses := [{ target := 0, region := (rows 0 2 14 14 16), good := (rows 28 14 14 14 16) },{ target := 1, region := (rows 15 0 4 8 31), good := (rows 29 29 29 29 16) }] }

theorem profile79_node32 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,6] 2 :=
  cut_bound_sound (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,6] 2 profile79_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10,6] 2 profile79_node32_cert).mp (by decide +kernel))

def profile79_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node30 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10] 2 (by decide) (choices 2) [5,6] profile79_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13,10] (choices 2) [5,6] profile79_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile79_node31
  · exact profile79_node32

def profile79_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node27 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13] 2 (by decide) (choices 2) [3,9,10] profile79_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28,13] (choices 2) [3,9,10] profile79_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile79_node28
  · exact profile79_node29
  · exact profile79_node30

def profile79_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node26 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28] 2 (by decide) (choices 3) [13] profile79_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [28] (choices 3) [13] profile79_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node27

def profile79_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node0 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [] 2 (by decide) (choices 3) [14,22,28] profile79_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [] (choices 3) [14,22,28] profile79_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile79_node1
  · exact profile79_node22
  · exact profile79_node26

theorem profile79 : Upper (D (n:=5) [50,50,36,35,33]) (R (n:=5) [50,50,36,35,33]) [] 2 := profile79_node0

def profile80_node3_cert : CutBound 5 := { lost := (rows 0 8 8 6 6), upper := (rows 31 7 7 25 25), lower := (rows 31 7 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile80_node3 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,3] 2 :=
  cut_bound_sound (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,3] 2 profile80_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,3] 2 profile80_node3_cert).mp (by decide +kernel))

def profile80_node4_cert : CutBound 5 := { lost := (rows 0 24 18 4 12), upper := (rows 31 7 13 27 19), lower := (rows 31 7 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile80_node4 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,9] 2 :=
  cut_bound_sound (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,9] 2 profile80_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5,9] 2 profile80_node4_cert).mp (by decide +kernel))

def profile80_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile80_node2 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5] 2 (by decide) (choices 2) [3,9] profile80_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30,5] (choices 2) [3,9] profile80_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile80_node3
  · exact profile80_node4

def profile80_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile80_node1 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30] 2 (by decide) (choices 2) [5] profile80_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [30] (choices 2) [5] profile80_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node2

def profile80_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node0 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [] 2 (by decide) (choices 4) [30] profile80_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [] (choices 4) [30] profile80_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node1

theorem profile80 : Upper (D (n:=5) [68,34,34,34,34]) (R (n:=5) [68,34,34,34,34]) [] 2 := profile80_node0

def profile81_node3_cert : CutBound 5 := { lost := (rows 0 24 24 4 4), upper := (rows 31 7 7 27 27), lower := (rows 31 7 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile81_node3 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,3] 2 :=
  cut_bound_sound (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,3] 2 profile81_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,3] 2 profile81_node3_cert).mp (by decide +kernel))

def profile81_node4_cert : CutBound 5 := { lost := (rows 0 24 18 4 12), upper := (rows 31 7 13 27 19), lower := (rows 31 7 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile81_node4 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,9] 2 :=
  cut_bound_sound (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,9] 2 profile81_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,9] 2 profile81_node4_cert).mp (by decide +kernel))

def profile81_node5_cert : CutBound 5 := { lost := (rows 0 24 17 4 12), upper := (rows 31 7 14 27 19), lower := (rows 31 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 14 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile81_node5 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,10] 2 profile81_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,10] 2 profile81_node5_cert).mp (by decide +kernel))

def profile81_node6_cert : CutBound 5 := { lost := (rows 0 8 3 4 12), upper := (rows 31 7 28 11 19), lower := (rows 31 7 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) }] }

theorem profile81_node6 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,24] 2 :=
  cut_bound_sound (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,24] 2 profile81_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5,24] 2 profile81_node6_cert).mp (by decide +kernel))

def profile81_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile81_node2 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5] 2 (by decide) (choices 2) [3,9,10,24] profile81_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,5] (choices 2) [3,9,10,24] profile81_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile81_node3
  · exact profile81_node4
  · exact profile81_node5
  · exact profile81_node6

def profile81_node7_cert : CutBound 5 := { lost := (rows 0 17 8 4 12), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 14 4 8 0) }] }

theorem profile81_node7 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,12] 2 profile81_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30,12] 2 profile81_node7_cert).mp (by decide +kernel))

def profile81_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile81_node1 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30] 2 (by decide) (choices 2) [5,12] profile81_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [30] (choices 2) [5,12] profile81_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile81_node2
  · exact profile81_node7

def profile81_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node0 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [] 2 (by decide) (choices 4) [30] profile81_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [] (choices 4) [30] profile81_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile81_node1

theorem profile81 : Upper (D (n:=5) [67,35,34,34,34]) (R (n:=5) [67,35,34,34,34]) [] 2 := profile81_node0

def profile82_node3_cert : CutBound 5 := { lost := (rows 0 8 8 5 5), upper := (rows 31 7 7 26 26), lower := (rows 31 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile82_node3 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,3] 2 :=
  cut_bound_sound (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,3] 2 profile82_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,3] 2 profile82_node3_cert).mp (by decide +kernel))

def profile82_node4_cert : CutBound 5 := { lost := (rows 0 24 17 4 12), upper := (rows 31 7 14 27 19), lower := (rows 31 7 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 14 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile82_node4 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,10] 2 profile82_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5,10] 2 profile82_node4_cert).mp (by decide +kernel))

def profile82_node2_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile82_node2 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5] 2 (by decide) (choices 2) [3,10] profile82_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,5] (choices 2) [3,10] profile82_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node3
  · exact profile82_node4

def profile82_node5_cert : CutBound 5 := { lost := (rows 0 17 8 4 12), upper := (rows 31 14 23 27 19), lower := (rows 31 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 14 4 8 0) }] }

theorem profile82_node5 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,12] 2 profile82_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30,12] 2 profile82_node5_cert).mp (by decide +kernel))

def profile82_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile82_node1 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30] 2 (by decide) (choices 2) [5,12] profile82_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [30] (choices 2) [5,12] profile82_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile82_node2
  · exact profile82_node5

def profile82_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node0 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [] 2 (by decide) (choices 4) [30] profile82_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [] (choices 4) [30] profile82_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile82_node1

theorem profile82 : Upper (D (n:=5) [66,36,34,34,34]) (R (n:=5) [66,36,34,34,34]) [] 2 := profile82_node0

def profile83_node2_cert : CutBound 5 := { lost := (rows 16 16 8 4 12), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile83_node2 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,13] 2 profile83_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,13] 2 profile83_node2_cert).mp (by decide +kernel))

def profile83_node4_cert : CutBound 5 := { lost := (rows 0 0 24 6 6), upper := (rows 15 23 7 25 25), lower := (rows 15 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile83_node4 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,3] 2 profile83_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,3] 2 profile83_node4_cert).mp (by decide +kernel))

def profile83_node5_cert : CutBound 5 := { lost := (rows 0 8 18 4 12), upper := (rows 15 23 13 27 19), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile83_node5 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,9] 2 profile83_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,9] 2 profile83_node5_cert).mp (by decide +kernel))

def profile83_node6_cert : CutBound 5 := { lost := (rows 16 8 10 20 4), upper := (rows 15 23 21 11 27), lower := (rows 15 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile83_node6 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,17] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,17] 2 profile83_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21,17] 2 profile83_node6_cert).mp (by decide +kernel))

def profile83_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node3 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21] 2 (by decide) (choices 2) [3,9,17] profile83_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14,21] (choices 2) [3,9,17] profile83_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile83_node4
  · exact profile83_node5
  · exact profile83_node6

def profile83_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile83_node1 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14] 2 (by decide) (choices 3) [13,21] profile83_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [14] (choices 3) [13,21] profile83_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile83_node2
  · exact profile83_node3

def profile83_node9_cert : CutBound 5 := { lost := (rows 0 16 24 4 12), upper := (rows 29 15 7 27 19), lower := (rows 29 15 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile83_node9 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,3] 2 profile83_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,3] 2 profile83_node9_cert).mp (by decide +kernel))

def profile83_node10_cert : CutBound 5 := { lost := (rows 0 16 10 20 12), upper := (rows 29 15 21 11 19), lower := (rows 29 15 21 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 17 8 16) },{ target := 3, region := (rows 1 2 7 0 18), good := (rows 21 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile83_node10 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,17] 2 :=
  cut_bound_sound (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,17] 2 profile83_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13,17] 2 profile83_node10_cert).mp (by decide +kernel))

def profile83_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node8 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13] 2 (by decide) (choices 2) [3,17] profile83_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28,13] (choices 2) [3,17] profile83_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile83_node9
  · exact profile83_node10

def profile83_node7_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile83_node7 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28] 2 (by decide) (choices 3) [13] profile83_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [28] (choices 3) [13] profile83_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node8

def profile83_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile83_node0 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [] 2 (by decide) (choices 3) [14,28] profile83_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [] (choices 3) [14,28] profile83_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile83_node1
  · exact profile83_node7

theorem profile83 : Upper (D (n:=5) [52,50,34,34,34]) (R (n:=5) [52,50,34,34,34]) [] 2 := profile83_node0

def profile84_node2_cert : CutBound 5 := { lost := (rows 16 16 8 4 12), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile84_node2 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,13] 2 profile84_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,13] 2 profile84_node2_cert).mp (by decide +kernel))

def profile84_node5_cert : CutBound 5 := { lost := (rows 0 8 8 6 5), upper := (rows 15 23 7 25 26), lower := (rows 15 23 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 24 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 13 25 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 25 16) },{ target := 3, region := (rows 1 10 15 0 16), good := (rows 7 23 7 23 16) }] }

theorem profile84_node5 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,17] 2 profile84_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,17] 2 profile84_node5_cert).mp (by decide +kernel))

def profile84_node6_cert : CutBound 5 := { lost := (rows 16 0 24 5 6), upper := (rows 15 23 7 26 25), lower := (rows 15 23 7 26 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 24 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 26 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 7 23 7 22 16) },{ target := 4, region := (rows 9 2 15 8 0), good := (rows 15 7 7 15 0) }] }

theorem profile84_node6 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,18] 2 profile84_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3,18] 2 profile84_node6_cert).mp (by decide +kernel))

def profile84_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node4 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3] 2 (by decide) (choices 2) [17,18] profile84_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,3] (choices 2) [17,18] profile84_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node5
  · exact profile84_node6

def profile84_node7_cert : CutBound 5 := { lost := (rows 0 8 18 4 12), upper := (rows 15 23 13 27 19), lower := (rows 15 23 13 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 13 21 13 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 7 13 8 0) }] }

theorem profile84_node7 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,9] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,9] 2 profile84_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,9] 2 profile84_node7_cert).mp (by decide +kernel))

def profile84_node8_cert : CutBound 5 := { lost := (rows 16 8 17 4 12), upper := (rows 15 23 14 27 19), lower := (rows 15 23 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile84_node8 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,10] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,10] 2 profile84_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,10] 2 profile84_node8_cert).mp (by decide +kernel))

def profile84_node9_cert : CutBound 5 := { lost := (rows 16 8 10 20 4), upper := (rows 15 23 21 11 27), lower := (rows 15 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 21 21 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile84_node9 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,17] 2 profile84_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,17] 2 profile84_node9_cert).mp (by decide +kernel))

def profile84_node10_cert : CutBound 5 := { lost := (rows 16 0 9 20 4), upper := (rows 15 23 22 11 27), lower := (rows 15 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 22 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile84_node10 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,18] 2 profile84_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,18] 2 profile84_node10_cert).mp (by decide +kernel))

def profile84_node11_cert : CutBound 5 := { lost := (rows 16 8 0 20 12), upper := (rows 15 23 28 11 19), lower := (rows 15 23 28 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile84_node11 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,24] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,24] 2 profile84_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21,24] 2 profile84_node11_cert).mp (by decide +kernel))

def profile84_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node3 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile84_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,21] (choices 2) [3,9,10,17,18,24] profile84_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile84_node4
  · exact profile84_node7
  · exact profile84_node8
  · exact profile84_node9
  · exact profile84_node10
  · exact profile84_node11

def profile84_node13_cert : CutBound 5 := { lost := (rows 16 0 24 4 12), upper := (rows 15 30 7 27 19), lower := (rows 15 30 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 3 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile84_node13 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,3] 2 profile84_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,3] 2 profile84_node13_cert).mp (by decide +kernel))

def profile84_node14_cert : CutBound 5 := { lost := (rows 16 0 8 20 12), upper := (rows 15 30 21 11 19), lower := (rows 15 30 21 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile84_node14 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,17] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,17] 2 profile84_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28,17] 2 profile84_node14_cert).mp (by decide +kernel))

def profile84_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node12 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28] 2 (by decide) (choices 2) [3,17] profile84_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14,28] (choices 2) [3,17] profile84_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node13
  · exact profile84_node14

def profile84_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile84_node1 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile84_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [14] (choices 3) [13,21,28] profile84_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile84_node2
  · exact profile84_node3
  · exact profile84_node12

def profile84_node17_cert : CutBound 5 := { lost := (rows 0 16 24 4 12), upper := (rows 29 15 7 27 19), lower := (rows 29 15 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 2 6 0 22), good := (rows 21 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile84_node17 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,3] 2 profile84_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,3] 2 profile84_node17_cert).mp (by decide +kernel))

def profile84_node18_cert : CutBound 5 := { lost := (rows 0 16 8 20 12), upper := (rows 29 15 22 11 19), lower := (rows 29 15 22 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 26 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile84_node18 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,18] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,18] 2 profile84_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13,18] 2 profile84_node18_cert).mp (by decide +kernel))

def profile84_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node16 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13] 2 (by decide) (choices 2) [3,18] profile84_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,13] (choices 2) [3,18] profile84_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node17
  · exact profile84_node18

def profile84_node20_cert : CutBound 5 := { lost := (rows 2 1 0 20 12), upper := (rows 29 30 7 11 19), lower := (rows 29 30 7 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 6 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 5 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 20), good := (rows 21 22 23 0 16) },{ target := 4, region := (rows 1 2 4 12 0), good := (rows 13 14 15 8 0) }] }

theorem profile84_node20 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28,3] 2 :=
  cut_bound_sound (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28,3] 2 profile84_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28,3] 2 profile84_node20_cert).mp (by decide +kernel))

def profile84_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node19 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28] 2 (by decide) (choices 2) [3] profile84_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28,28] (choices 2) [3] profile84_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node20

def profile84_node15_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 25 => (13,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile84_node15 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28] 2 (by decide) (choices 3) [13,28] profile84_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [28] (choices 3) [13,28] profile84_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node16
  · exact profile84_node19

def profile84_node0_route : Route 5 := (fun mask => match mask with | 22 => (14,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 26 => (14,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile84_node0 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [] 2 (by decide) (choices 3) [14,28] profile84_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [] (choices 3) [14,28] profile84_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node1
  · exact profile84_node15

theorem profile84 : Upper (D (n:=5) [51,51,34,34,34]) (R (n:=5) [51,51,34,34,34]) [] 2 := profile84_node0

def profile85_node3_cert : CutBound 5 := { lost := (rows 0 24 24 1 1), upper := (rows 31 7 7 30 30), lower := (rows 31 7 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 7 7 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 7 7 8 0) }] }

theorem profile85_node3 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,3] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,3] 2 profile85_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,3] 2 profile85_node3_cert).mp (by decide +kernel))

def profile85_node4_cert : CutBound 5 := { lost := (rows 0 24 18 1 9), upper := (rows 31 7 13 30 22), lower := (rows 31 7 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 13 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile85_node4 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,9] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,9] 2 profile85_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,9] 2 profile85_node4_cert).mp (by decide +kernel))

def profile85_node6_cert : CutBound 5 := { lost := (rows 0 8 1 6 9), upper := (rows 31 7 14 25 22), lower := (rows 31 7 14 25 16), losses := [{ target := 0, region := (rows 0 2 5 8 23), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 12 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 25 16) },{ target := 3, region := (rows 1 3 4 0 23), good := (rows 23 23 22 19 16) }] }

theorem profile85_node6 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,17] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,17] 2 profile85_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,17] 2 profile85_node6_cert).mp (by decide +kernel))

def profile85_node7_cert : CutBound 5 := { lost := (rows 0 8 1 5 10), upper := (rows 31 7 14 26 21), lower := (rows 31 7 14 26 16), losses := [{ target := 0, region := (rows 0 2 15 9 16), good := (rows 30 14 14 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 21 28 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 10 26 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 18 16) }] }

theorem profile85_node7 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,18] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,18] 2 profile85_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,18] 2 profile85_node7_cert).mp (by decide +kernel))

def profile85_node8_cert : CutBound 5 := { lost := (rows 0 8 1 3 12), upper := (rows 31 7 14 28 19), lower := (rows 31 7 14 28 16), losses := [{ target := 0, region := (rows 0 2 7 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 12 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 26 24 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 20 16) }] }

theorem profile85_node8 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,20] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,20] 2 profile85_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10,20] 2 profile85_node8_cert).mp (by decide +kernel))

def profile85_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node5 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10] 2 (by decide) (choices 2) [17,18,20] profile85_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,10] (choices 2) [17,18,20] profile85_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node6
  · exact profile85_node7
  · exact profile85_node8

def profile85_node9_cert : CutBound 5 := { lost := (rows 0 24 3 16 8), upper := (rows 31 7 28 15 23), lower := (rows 31 7 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 6 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 5 28 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile85_node9 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,24] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,24] 2 profile85_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5,24] 2 profile85_node9_cert).mp (by decide +kernel))

def profile85_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile85_node2 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5] 2 (by decide) (choices 2) [3,9,10,24] profile85_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,5] (choices 2) [3,9,10,24] profile85_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile85_node3
  · exact profile85_node4
  · exact profile85_node5
  · exact profile85_node9

def profile85_node11_cert : CutBound 5 := { lost := (rows 0 20 24 1 9), upper := (rows 31 11 7 30 22), lower := (rows 31 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 3 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile85_node11 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,3] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,3] 2 profile85_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,3] 2 profile85_node11_cert).mp (by decide +kernel))

def profile85_node12_cert : CutBound 5 := { lost := (rows 0 4 10 1 9), upper := (rows 31 11 21 14 22), lower := (rows 31 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 19 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile85_node12 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,17] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,17] 2 profile85_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,17] 2 profile85_node12_cert).mp (by decide +kernel))

def profile85_node13_cert : CutBound 5 := { lost := (rows 0 20 9 16 8), upper := (rows 31 11 22 15 23), lower := (rows 31 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 18 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 11 6 8 0) }] }

theorem profile85_node13 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,18] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,18] 2 profile85_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9,18] 2 profile85_node13_cert).mp (by decide +kernel))

def profile85_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node10 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9] 2 (by decide) (choices 2) [3,17,18] profile85_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,9] (choices 2) [3,17,18] profile85_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node11
  · exact profile85_node12
  · exact profile85_node13

def profile85_node16_cert : CutBound 5 := { lost := (rows 0 1 8 6 9), upper := (rows 31 14 7 25 22), lower := (rows 31 14 7 25 16), losses := [{ target := 0, region := (rows 0 3 4 8 23), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 12 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 10 11 25 16) },{ target := 3, region := (rows 1 2 5 0 23), good := (rows 23 22 23 21 16) }] }

theorem profile85_node16 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,17] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,17] 2 profile85_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,17] 2 profile85_node16_cert).mp (by decide +kernel))

def profile85_node17_cert : CutBound 5 := { lost := (rows 0 1 8 5 10), upper := (rows 31 14 7 26 21), lower := (rows 31 14 7 26 16), losses := [{ target := 0, region := (rows 0 7 4 9 16), good := (rows 30 14 14 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 21 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 10 11 26 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 18 16) }] }

theorem profile85_node17 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,18] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,18] 2 profile85_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,18] 2 profile85_node17_cert).mp (by decide +kernel))

def profile85_node18_cert : CutBound 5 := { lost := (rows 0 1 8 3 12), upper := (rows 31 14 7 28 19), lower := (rows 31 14 7 28 16), losses := [{ target := 0, region := (rows 0 15 4 9 16), good := (rows 30 14 14 30 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 12 13 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 19 24 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 20 16) }] }

theorem profile85_node18 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,20] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,20] 2 profile85_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3,20] 2 profile85_node18_cert).mp (by decide +kernel))

def profile85_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node15 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3] 2 (by decide) (choices 2) [17,18,20] profile85_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,3] (choices 2) [17,18,20] profile85_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node16
  · exact profile85_node17
  · exact profile85_node18

def profile85_node19_cert : CutBound 5 := { lost := (rows 0 17 10 16 8), upper := (rows 31 14 21 15 23), lower := (rows 31 14 21 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 12 21 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 21 0 16) },{ target := 4, region := (rows 1 7 4 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile85_node19 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,17] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,17] 2 profile85_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,17] 2 profile85_node19_cert).mp (by decide +kernel))

def profile85_node20_cert : CutBound 5 := { lost := (rows 0 17 9 16 8), upper := (rows 31 14 22 15 23), lower := (rows 31 14 22 8 16), losses := [{ target := 0, region := (rows 0 3 5 8 16), good := (rows 30 14 22 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 22 0 16) },{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 14 6 8 0) }] }

theorem profile85_node20 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,18] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,18] 2 profile85_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12,18] 2 profile85_node20_cert).mp (by decide +kernel))

def profile85_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node14 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12] 2 (by decide) (choices 2) [3,17,18] profile85_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,12] (choices 2) [3,17,18] profile85_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node15
  · exact profile85_node19
  · exact profile85_node20

def profile85_node21_cert : CutBound 5 := { lost := (rows 0 5 24 16 8), upper := (rows 31 26 7 15 23), lower := (rows 31 26 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 26 4 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 18 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile85_node21 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,24] 2 :=
  cut_bound_sound (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,24] 2 profile85_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30,24] 2 profile85_node21_cert).mp (by decide +kernel))

def profile85_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile85_node1 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30] 2 (by decide) (choices 2) [5,9,12,24] profile85_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [30] (choices 2) [5,9,12,24] profile85_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile85_node2
  · exact profile85_node10
  · exact profile85_node14
  · exact profile85_node21

def profile85_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node0 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [] 2 (by decide) (choices 4) [30] profile85_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [] (choices 4) [30] profile85_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node1

theorem profile85 : Upper (D (n:=5) [66,35,35,34,34]) (R (n:=5) [66,35,35,34,34]) [] 2 := profile85_node0

def profile86_node3_cert : CutBound 5 := { lost := (rows 0 24 16 0 8), upper := (rows 31 7 14 30 22), lower := (rows 31 7 14 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 23), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 5 8 0), good := (rows 15 7 14 8 0) }] }

theorem profile86_node3 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5,10] 2 :=
  cut_bound_sound (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5,10] 2 profile86_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5,10] 2 profile86_node3_cert).mp (by decide +kernel))

def profile86_node2_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile86_node2 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5] 2 := by
  apply routed_branch (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5] 2 (by decide) (choices 2) [10] profile86_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,5] (choices 2) [10] profile86_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node3

def profile86_node4_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 31 11 22 30 22), lower := (rows 31 11 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 11 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile86_node4 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,9] 2 :=
  cut_bound_sound (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,9] 2 profile86_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,9] 2 profile86_node4_cert).mp (by decide +kernel))

def profile86_node5_cert : CutBound 5 := { lost := (rows 0 16 8 0 8), upper := (rows 31 14 23 31 23), lower := (rows 31 14 4 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 6 4 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 14 4 8 0) }] }

theorem profile86_node5 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,12] 2 :=
  cut_bound_sound (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,12] 2 profile86_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,12] 2 profile86_node5_cert).mp (by decide +kernel))

def profile86_node6_cert : CutBound 5 := { lost := (rows 0 4 8 0 8), upper := (rows 31 26 7 15 23), lower := (rows 31 26 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 18 4 0 16) }] }

theorem profile86_node6 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,24] 2 :=
  cut_bound_sound (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,24] 2 profile86_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30,24] 2 profile86_node6_cert).mp (by decide +kernel))

def profile86_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile86_node1 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30] 2 (by decide) (choices 2) [5,9,12,24] profile86_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [30] (choices 2) [5,9,12,24] profile86_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile86_node2
  · exact profile86_node4
  · exact profile86_node5
  · exact profile86_node6

def profile86_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node0 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [] 2 (by decide) (choices 4) [30] profile86_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [] (choices 4) [30] profile86_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node1

theorem profile86 : Upper (D (n:=5) [65,36,35,34,34]) (R (n:=5) [65,36,35,34,34]) [] 2 := profile86_node0

#print axioms profile86
end Delivery.FiveVertexPositive12
