import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile10_node2 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,5] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,5] 3 profile10_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,5] 3 profile10_node2_cert).mp (by decide +kernel))

def profile10_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 7 11 7 29 21), lower := (rows 7 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile10_node4 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,3] 3 profile10_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,3] 3 profile10_node4_cert).mp (by decide +kernel))

def profile10_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 2), upper := (rows 7 11 21 11 21), lower := (rows 7 11 21 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 21 29 21 29 16) }] }

theorem profile10_node6 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,3] 3 profile10_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,3] 3 profile10_node6_cert).mp (by decide +kernel))

def profile10_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 11 21 13 19), lower := (rows 7 11 21 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 9 29 13 16) }] }

theorem profile10_node7 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,5] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,5] 3 profile10_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17,5] 3 profile10_node7_cert).mp (by decide +kernel))

def profile10_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node5 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17] 3 (by decide) (choices 2) [3,5] profile10_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9,17] (choices 2) [3,5] profile10_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node6
  · exact profile10_node7

def profile10_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node3 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9] 3 (by decide) (choices 2) [3,17] profile10_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6,9] (choices 2) [3,17] profile10_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node4
  · exact profile10_node5

def profile10_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile10_node1 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6] 3 (by decide) (choices 2) [5,9] profile10_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [6] (choices 2) [5,9] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node2
  · exact profile10_node3

def profile10_node10_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 11 7 7 29 21), lower := (rows 11 7 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile10_node10 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,3] 3 profile10_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,3] 3 profile10_node10_cert).mp (by decide +kernel))

def profile10_node12_cert : CutBound 5 := { lost := (rows 0 0 2 0 2), upper := (rows 11 7 21 11 21), lower := (rows 11 7 21 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 21 21 29 16) }] }

theorem profile10_node12 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,3] 3 profile10_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,3] 3 profile10_node12_cert).mp (by decide +kernel))

def profile10_node13_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 11 7 21 13 19), lower := (rows 11 7 21 13 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 9 13 29 13 16) }] }

theorem profile10_node13 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,5] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,5] 3 profile10_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17,5] 3 profile10_node13_cert).mp (by decide +kernel))

def profile10_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node11 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17] 3 (by decide) (choices 2) [3,5] profile10_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5,17] (choices 2) [3,5] profile10_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node12
  · exact profile10_node13

def profile10_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node9 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5] 3 (by decide) (choices 2) [3,17] profile10_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,5] (choices 2) [3,17] profile10_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node10
  · exact profile10_node11

def profile10_node15_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 11 19 7 13 21), lower := (rows 11 19 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 12 20), good := (rows 9 17 29 8 16) }] }

theorem profile10_node15 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17,3] 3 profile10_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17,3] 3 profile10_node15_cert).mp (by decide +kernel))

def profile10_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node14 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17] 3 (by decide) (choices 2) [3] profile10_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10,17] (choices 2) [3] profile10_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node15

def profile10_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node8 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10] 3 (by decide) (choices 2) [5,17] profile10_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [10] (choices 2) [5,17] profile10_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node9
  · exact profile10_node14

def profile10_node19_cert : CutBound 5 := { lost := (rows 2 0 0 0 2), upper := (rows 25 7 7 11 21), lower := (rows 25 7 7 11 16), losses := [{ target := 1, region := (rows 9 0 4 8 22), good := (rows 25 21 21 25 16) }] }

theorem profile10_node19 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,3] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,3] 3 profile10_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,3] 3 profile10_node19_cert).mp (by decide +kernel))

def profile10_node20_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 25 7 7 13 19), lower := (rows 25 7 7 13 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 13 13 13 16) }] }

theorem profile10_node20 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,5] 3 :=
  cut_bound_sound (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,5] 3 profile10_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3,5] 3 profile10_node20_cert).mp (by decide +kernel))

def profile10_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node18 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3] 3 (by decide) (choices 2) [3,5] profile10_node18_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5,3] (choices 2) [3,5] profile10_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile10_node19
  · exact profile10_node20

def profile10_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node17 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5] 3 (by decide) (choices 2) [3] profile10_node17_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24,5] (choices 2) [3] profile10_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node18

def profile10_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node16 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24] 3 (by decide) (choices 2) [5] profile10_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [24] (choices 2) [5] profile10_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node17

def profile10_node0_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile10_node0 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [] 3 := by
  apply routed_branch (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [] 3 (by decide) (choices 2) [6,10,24] profile10_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [] (choices 2) [6,10,24] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node1
  · exact profile10_node8
  · exact profile10_node16

theorem profile10 : Upper (D (n:=5) [36,34,34,33,33]) (R (n:=5) [36,34,34,33,33]) [] 3 := profile10_node0

def profile11_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile11_node2 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,5] 3 profile11_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,5] 3 profile11_node2_cert).mp (by decide +kernel))

def profile11_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 7 11 7 25 22), lower := (rows 7 11 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 22 26 22 24 16) }] }

theorem profile11_node5 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,17] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,17] 3 profile11_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,17] 3 profile11_node5_cert).mp (by decide +kernel))

def profile11_node6_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 7 11 7 26 21), lower := (rows 7 11 7 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 25 21 24 16) }] }

theorem profile11_node6 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,18] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,18] 3 profile11_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,18] 3 profile11_node6_cert).mp (by decide +kernel))

def profile11_node7_cert : CutBound 5 := { lost := (rows 0 0 0 0 4), upper := (rows 7 11 7 28 19), lower := (rows 7 11 7 28 16), losses := [{ target := 2, region := (rows 1 2 0 8 23), good := (rows 19 27 19 24 16) }] }

theorem profile11_node7 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,20] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,20] 3 profile11_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3,20] 3 profile11_node7_cert).mp (by decide +kernel))

def profile11_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node4 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3] 3 (by decide) (choices 2) [17,18,20] profile11_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,3] (choices 2) [17,18,20] profile11_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node5
  · exact profile11_node6
  · exact profile11_node7

def profile11_node9_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 7 11 21 11 22), lower := (rows 7 11 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 22 26 20 26 16) }] }

theorem profile11_node9 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,3] 3 profile11_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,3] 3 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 7 11 21 14 19), lower := (rows 7 11 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 10 28 14 16) }] }

theorem profile11_node10 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,6] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,6] 3 profile11_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17,6] 3 profile11_node10_cert).mp (by decide +kernel))

def profile11_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node8 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17] 3 (by decide) (choices 2) [3,6] profile11_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,17] (choices 2) [3,6] profile11_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node9
  · exact profile11_node10

def profile11_node12_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 7 11 22 11 21), lower := (rows 7 11 22 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 17), good := (rows 21 25 20 25 16) }] }

theorem profile11_node12 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,3] 3 profile11_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,3] 3 profile11_node12_cert).mp (by decide +kernel))

def profile11_node13_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 11 22 13 19), lower := (rows 7 11 22 13 16), losses := [{ target := 1, region := (rows 1 0 4 9 16), good := (rows 13 9 20 13 16) }] }

theorem profile11_node13 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,5] 3 profile11_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18,5] 3 profile11_node13_cert).mp (by decide +kernel))

def profile11_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node11 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18] 3 (by decide) (choices 2) [3,5] profile11_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9,18] (choices 2) [3,5] profile11_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node12
  · exact profile11_node13

def profile11_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node3 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9] 3 (by decide) (choices 2) [3,17,18] profile11_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,9] (choices 2) [3,17,18] profile11_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node4
  · exact profile11_node8
  · exact profile11_node11

def profile11_node14_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 7 14 23 27 19), lower := (rows 7 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile11_node14 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,12] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,12] 3 profile11_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,12] 3 profile11_node14_cert).mp (by decide +kernel))

def profile11_node17_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 7 26 7 11 21), lower := (rows 7 26 7 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 24 21 25 16) }] }

theorem profile11_node17 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,3] 3 profile11_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,3] 3 profile11_node17_cert).mp (by decide +kernel))

def profile11_node18_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 7 26 7 13 19), lower := (rows 7 26 7 13 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 24 13 13 16) }] }

theorem profile11_node18 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,5] 3 profile11_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3,5] 3 profile11_node18_cert).mp (by decide +kernel))

def profile11_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node16 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3] 3 (by decide) (choices 2) [3,5] profile11_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24,3] (choices 2) [3,5] profile11_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node17
  · exact profile11_node18

def profile11_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node15 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24] 3 (by decide) (choices 2) [3] profile11_node15_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6,24] (choices 2) [3] profile11_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node16

def profile11_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile11_node1 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6] 3 (by decide) (choices 2) [5,9,12,24] profile11_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [6] (choices 2) [5,9,12,24] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node2
  · exact profile11_node3
  · exact profile11_node14
  · exact profile11_node15

def profile11_node22_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 11 7 7 25 22), lower := (rows 11 7 7 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 22 22 24 16) }] }

theorem profile11_node22 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,17] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,17] 3 profile11_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,17] 3 profile11_node22_cert).mp (by decide +kernel))

def profile11_node23_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 11 7 7 26 21), lower := (rows 11 7 7 26 16), losses := [{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 21 21 24 16) }] }

theorem profile11_node23 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,18] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,18] 3 profile11_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,18] 3 profile11_node23_cert).mp (by decide +kernel))

def profile11_node24_cert : CutBound 5 := { lost := (rows 0 0 0 0 4), upper := (rows 11 7 7 28 19), lower := (rows 11 7 7 28 16), losses := [{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 19 19 24 16) }] }

theorem profile11_node24 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,20] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,20] 3 profile11_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3,20] 3 profile11_node24_cert).mp (by decide +kernel))

def profile11_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node21 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3] 3 (by decide) (choices 2) [17,18,20] profile11_node21_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,3] (choices 2) [17,18,20] profile11_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node22
  · exact profile11_node23
  · exact profile11_node24

def profile11_node26_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 11 7 21 11 22), lower := (rows 11 7 21 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 26 22 20 26 16) }] }

theorem profile11_node26 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,3] 3 profile11_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,3] 3 profile11_node26_cert).mp (by decide +kernel))

def profile11_node27_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 11 7 21 14 19), lower := (rows 11 7 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 10 14 20 14 16) }] }

theorem profile11_node27 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,6] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,6] 3 profile11_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17,6] 3 profile11_node27_cert).mp (by decide +kernel))

def profile11_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node25 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17] 3 (by decide) (choices 2) [3,6] profile11_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,17] (choices 2) [3,6] profile11_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node26
  · exact profile11_node27

def profile11_node29_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 11 7 22 11 21), lower := (rows 11 7 22 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 18), good := (rows 25 21 20 25 16) }] }

theorem profile11_node29 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,3] 3 profile11_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,3] 3 profile11_node29_cert).mp (by decide +kernel))

def profile11_node30_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 11 7 22 13 19), lower := (rows 11 7 22 13 16), losses := [{ target := 1, region := (rows 1 0 4 10 16), good := (rows 9 13 28 13 16) }] }

theorem profile11_node30 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,5] 3 profile11_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18,5] 3 profile11_node30_cert).mp (by decide +kernel))

def profile11_node28_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node28 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18] 3 (by decide) (choices 2) [3,5] profile11_node28_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5,18] (choices 2) [3,5] profile11_node28_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node29
  · exact profile11_node30

def profile11_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node20 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5] 3 (by decide) (choices 2) [3,17,18] profile11_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,5] (choices 2) [3,17,18] profile11_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node21
  · exact profile11_node25
  · exact profile11_node28

def profile11_node33_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 11 19 7 13 22), lower := (rows 11 19 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 10 18 22 28 16) }] }

theorem profile11_node33 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,5] 3 profile11_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,5] 3 profile11_node33_cert).mp (by decide +kernel))

def profile11_node34_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 11 19 7 14 21), lower := (rows 11 19 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 10 18 14 14 16) }] }

theorem profile11_node34 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,6] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,6] 3 profile11_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3,6] 3 profile11_node34_cert).mp (by decide +kernel))

def profile11_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node32 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3] 3 (by decide) (choices 2) [5,6] profile11_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17,3] (choices 2) [5,6] profile11_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node33
  · exact profile11_node34

def profile11_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node31 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17] 3 (by decide) (choices 2) [3] profile11_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,17] (choices 2) [3] profile11_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node32

def profile11_node37_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 11 22 7 11 21), lower := (rows 11 22 7 11 16), losses := [{ target := 1, region := (rows 1 0 4 8 20), good := (rows 9 20 21 9 16) }] }

theorem profile11_node37 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,3] 3 profile11_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,3] 3 profile11_node37_cert).mp (by decide +kernel))

def profile11_node38_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 11 22 7 13 19), lower := (rows 11 22 7 13 16), losses := [{ target := 1, region := (rows 1 0 4 12 16), good := (rows 9 28 13 13 16) }] }

theorem profile11_node38 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,5] 3 profile11_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3,5] 3 profile11_node38_cert).mp (by decide +kernel))

def profile11_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node36 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3] 3 (by decide) (choices 2) [3,5] profile11_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20,3] (choices 2) [3,5] profile11_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node37
  · exact profile11_node38

def profile11_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node35 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20] 3 (by decide) (choices 2) [3] profile11_node35_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10,20] (choices 2) [3] profile11_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node36

def profile11_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node19 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10] 3 (by decide) (choices 2) [5,17,20] profile11_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [10] (choices 2) [5,17,20] profile11_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node20
  · exact profile11_node31
  · exact profile11_node35

def profile11_node40_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 13 7 23 27 19), lower := (rows 13 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 9 27 0 8 16) }] }

theorem profile11_node40 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,5] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,5] 3 profile11_node40_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,5] 3 profile11_node40_cert).mp (by decide +kernel))

def profile11_node43_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 13 19 7 11 22), lower := (rows 13 19 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 28 18 22 10 16) }] }

theorem profile11_node43 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,3] 3 profile11_node43_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,3] 3 profile11_node43_cert).mp (by decide +kernel))

def profile11_node44_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 13 19 7 14 19), lower := (rows 13 19 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 12 18 14 14 16) }] }

theorem profile11_node44 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,6] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,6] 3 profile11_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3,6] 3 profile11_node44_cert).mp (by decide +kernel))

def profile11_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node42 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3] 3 (by decide) (choices 2) [3,6] profile11_node42_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17,3] (choices 2) [3,6] profile11_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node43
  · exact profile11_node44

def profile11_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node41 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17] 3 (by decide) (choices 2) [3] profile11_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,17] (choices 2) [3] profile11_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node42

def profile11_node46_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 13 22 7 11 19), lower := (rows 13 22 7 8 16), losses := [{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile11_node46 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20,3] 3 profile11_node46_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20,3] 3 profile11_node46_cert).mp (by decide +kernel))

def profile11_node45_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node45 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20] 3 (by decide) (choices 2) [3] profile11_node45_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12,20] (choices 2) [3] profile11_node45_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node46

def profile11_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node39 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12] 3 (by decide) (choices 2) [5,17,20] profile11_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [12] (choices 2) [5,17,20] profile11_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node40
  · exact profile11_node41
  · exact profile11_node45

def profile11_node50_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 25 7 7 11 22), lower := (rows 25 7 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 24 22 22 26 16) }] }

theorem profile11_node50 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,3] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,3] 3 profile11_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,3] 3 profile11_node50_cert).mp (by decide +kernel))

def profile11_node51_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 25 7 7 14 19), lower := (rows 25 7 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 24 14 14 14 16) }] }

theorem profile11_node51 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,6] 3 :=
  cut_bound_sound (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,6] 3 profile11_node51_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3,6] 3 profile11_node51_cert).mp (by decide +kernel))

def profile11_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node49 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3] 3 (by decide) (choices 2) [3,6] profile11_node49_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5,3] (choices 2) [3,6] profile11_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node50
  · exact profile11_node51

def profile11_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node48 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5] 3 (by decide) (choices 2) [3] profile11_node48_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24,5] (choices 2) [3] profile11_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node49

def profile11_node47_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node47 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24] 3 (by decide) (choices 2) [5] profile11_node47_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [24] (choices 2) [5] profile11_node47_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node48

def profile11_node0_route : Route 5 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile11_node0 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [] 3 := by
  apply routed_branch (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [] 3 (by decide) (choices 2) [6,10,12,24] profile11_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [] (choices 2) [6,10,12,24] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node1
  · exact profile11_node19
  · exact profile11_node39
  · exact profile11_node47

theorem profile11 : Upper (D (n:=5) [35,35,34,33,33]) (R (n:=5) [35,35,34,33,33]) [] 3 := profile11_node0

def profile12_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile12_node2 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 3 profile12_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,5] 3 profile12_node2_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 5 := { lost := (rows 8 0 8 2 2), upper := (rows 7 11 7 29 29), lower := (rows 7 11 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile12_node4 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 3 profile12_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,3] 3 profile12_node4_cert).mp (by decide +kernel))

def profile12_node6_cert : CutBound 5 := { lost := (rows 0 4 2 0 9), upper := (rows 7 11 13 25 22), lower := (rows 7 11 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 22 26 28 24 16) },{ target := 1, region := (rows 1 0 14 8 16), good := (rows 5 13 13 29 16) },{ target := 2, region := (rows 1 14 0 8 16), good := (rows 3 11 11 27 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 17 16) }] }

theorem profile12_node6 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,17] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,17] 3 profile12_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,17] 3 profile12_node6_cert).mp (by decide +kernel))

def profile12_node7_cert : CutBound 5 := { lost := (rows 0 4 2 0 10), upper := (rows 7 11 13 26 21), lower := (rows 7 11 13 26 16), losses := [{ target := 1, region := (rows 1 0 6 8 23), good := (rows 21 29 29 28 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 3 11 11 26 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 21 18 16) }] }

theorem profile12_node7 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,18] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,18] 3 profile12_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,18] 3 profile12_node7_cert).mp (by decide +kernel))

def profile12_node8_cert : CutBound 5 := { lost := (rows 0 4 2 0 12), upper := (rows 7 11 13 28 19), lower := (rows 7 11 13 28 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 13 13 28 16) },{ target := 2, region := (rows 1 6 0 8 23), good := (rows 19 27 27 26 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 21 20 16) }] }

theorem profile12_node8 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,20] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,20] 3 profile12_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9,20] 3 profile12_node8_cert).mp (by decide +kernel))

def profile12_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node5 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] 3 (by decide) (choices 2) [17,18,20] profile12_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,9] (choices 2) [17,18,20] profile12_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node6
  · exact profile12_node7
  · exact profile12_node8

def profile12_node9_cert : CutBound 5 := { lost := (rows 8 0 1 2 10), upper := (rows 7 11 14 29 21), lower := (rows 7 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 14 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile12_node9 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 3 profile12_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,10] 3 profile12_node9_cert).mp (by decide +kernel))

def profile12_node11_cert : CutBound 5 := { lost := (rows 0 4 2 4 2), upper := (rows 7 11 21 11 28), lower := (rows 7 11 21 11 16), losses := [{ target := 1, region := (rows 1 0 15 8 26), good := (rows 21 29 21 29 16) },{ target := 2, region := (rows 1 15 0 15 16), good := (rows 11 11 27 11 16) }] }

theorem profile12_node11 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 3 profile12_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,3] 3 profile12_node11_cert).mp (by decide +kernel))

def profile12_node12_cert : CutBound 5 := { lost := (rows 0 4 0 2 5), upper := (rows 7 11 21 13 26), lower := (rows 7 11 21 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 26 20 12 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 13 9 29 13 16) },{ target := 2, region := (rows 1 10 0 8 26), good := (rows 19 27 17 27 16) }] }

theorem profile12_node12 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 3 profile12_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,5] 3 profile12_node12_cert).mp (by decide +kernel))

def profile12_node13_cert : CutBound 5 := { lost := (rows 0 0 2 1 6), upper := (rows 7 11 21 14 25), lower := (rows 7 11 21 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 10 28 14 16) },{ target := 1, region := (rows 1 0 7 8 18), good := (rows 21 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 17 26 16) }] }

theorem profile12_node13 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 3 profile12_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17,6] 3 profile12_node13_cert).mp (by decide +kernel))

def profile12_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node10 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17] 3 (by decide) (choices 2) [3,5,6] profile12_node10_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,17] (choices 2) [3,5,6] profile12_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node11
  · exact profile12_node12
  · exact profile12_node13

def profile12_node15_cert : CutBound 5 := { lost := (rows 0 4 0 2 6), upper := (rows 7 11 22 13 25), lower := (rows 7 11 22 13 16), losses := [{ target := 1, region := (rows 1 0 4 9 27), good := (rows 29 25 20 29 16) },{ target := 2, region := (rows 1 10 0 8 26), good := (rows 19 27 18 27 16) }] }

theorem profile12_node15 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18,5] 3 profile12_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18,5] 3 profile12_node15_cert).mp (by decide +kernel))

def profile12_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node14 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] 3 (by decide) (choices 2) [5] profile12_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,18] (choices 2) [5] profile12_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node15

def profile12_node17_cert : CutBound 5 := { lost := (rows 0 4 2 4 2), upper := (rows 7 11 28 11 21), lower := (rows 7 11 28 11 16), losses := [{ target := 1, region := (rows 1 0 14 8 27), good := (rows 21 29 28 29 16) },{ target := 2, region := (rows 1 11 0 11 16), good := (rows 11 11 26 11 16) }] }

theorem profile12_node17 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,3] 3 profile12_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,3] 3 profile12_node17_cert).mp (by decide +kernel))

def profile12_node18_cert : CutBound 5 := { lost := (rows 0 4 0 2 12), upper := (rows 7 11 28 13 19), lower := (rows 7 11 28 13 16), losses := [{ target := 1, region := (rows 1 0 4 9 16), good := (rows 13 9 28 13 16) },{ target := 2, region := (rows 1 10 0 8 27), good := (rows 19 27 26 27 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 20 21 16) }] }

theorem profile12_node18 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,5] 3 profile12_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24,5] 3 profile12_node18_cert).mp (by decide +kernel))

def profile12_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node16 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] 3 (by decide) (choices 2) [3,5] profile12_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9,24] (choices 2) [3,5] profile12_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node17
  · exact profile12_node18

def profile12_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node3 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9] 3 (by decide) (choices 2) [3,9,10,17,18,24] profile12_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,9] (choices 2) [3,9,10,17,18,24] profile12_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node4
  · exact profile12_node5
  · exact profile12_node9
  · exact profile12_node10
  · exact profile12_node14
  · exact profile12_node16

def profile12_node20_cert : CutBound 5 := { lost := (rows 0 0 0 6 6), upper := (rows 7 14 7 25 25), lower := (rows 7 14 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) }] }

theorem profile12_node20 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,3] 3 profile12_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,3] 3 profile12_node20_cert).mp (by decide +kernel))

def profile12_node21_cert : CutBound 5 := { lost := (rows 8 1 0 4 12), upper := (rows 7 14 13 27 19), lower := (rows 7 14 13 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 6 14 14 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile12_node21 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,9] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,9] 3 profile12_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,9] 3 profile12_node21_cert).mp (by decide +kernel))

def profile12_node23_cert : CutBound 5 := { lost := (rows 0 0 2 4 6), upper := (rows 7 14 21 11 25), lower := (rows 7 14 21 11 16), losses := [{ target := 1, region := (rows 1 0 12 8 24), good := (rows 5 28 21 29 16) },{ target := 2, region := (rows 1 2 0 9 29), good := (rows 27 26 25 27 16) }] }

theorem profile12_node23 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17,3] 3 profile12_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17,3] 3 profile12_node23_cert).mp (by decide +kernel))

def profile12_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node22 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17] 3 (by decide) (choices 2) [3] profile12_node22_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12,17] (choices 2) [3] profile12_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node23

def profile12_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node19 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] 3 (by decide) (choices 2) [3,9,17] profile12_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,12] (choices 2) [3,9,17] profile12_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node20
  · exact profile12_node21
  · exact profile12_node22

def profile12_node26_cert : CutBound 5 := { lost := (rows 0 0 2 4 3), upper := (rows 7 19 13 11 28), lower := (rows 7 19 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 18 28 10 16) },{ target := 1, region := (rows 1 0 12 8 28), good := (rows 21 17 29 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 11 27 9 11 16) }] }

theorem profile12_node26 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 3 profile12_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,3] 3 profile12_node26_cert).mp (by decide +kernel))

def profile12_node27_cert : CutBound 5 := { lost := (rows 0 4 2 2 4), upper := (rows 7 19 13 13 26), lower := (rows 7 19 13 13 16), losses := [{ target := 1, region := (rows 1 0 15 15 16), good := (rows 13 29 13 13 16) },{ target := 2, region := (rows 1 15 0 8 28), good := (rows 19 19 27 27 16) }] }

theorem profile12_node27 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 3 profile12_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,5] 3 profile12_node27_cert).mp (by decide +kernel))

def profile12_node28_cert : CutBound 5 := { lost := (rows 0 4 0 1 6), upper := (rows 7 19 13 14 25), lower := (rows 7 19 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 14 26 12 14 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 17 29 28 16) },{ target := 2, region := (rows 1 7 0 8 20), good := (rows 19 19 27 26 16) }] }

theorem profile12_node28 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 3 profile12_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9,6] 3 profile12_node28_cert).mp (by decide +kernel))

def profile12_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node25 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9] 3 (by decide) (choices 2) [3,5,6] profile12_node25_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,9] (choices 2) [3,5,6] profile12_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node26
  · exact profile12_node27
  · exact profile12_node28

def profile12_node30_cert : CutBound 5 := { lost := (rows 0 4 0 2 6), upper := (rows 7 19 14 13 25), lower := (rows 7 19 14 13 16), losses := [{ target := 1, region := (rows 1 0 4 9 27), good := (rows 29 25 28 29 16) },{ target := 2, region := (rows 1 10 0 8 24), good := (rows 3 19 26 27 16) }] }

theorem profile12_node30 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10,5] 3 profile12_node30_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10,5] 3 profile12_node30_cert).mp (by decide +kernel))

def profile12_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node29 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] 3 (by decide) (choices 2) [5] profile12_node29_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17,10] (choices 2) [5] profile12_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node30

def profile12_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node24 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17] 3 (by decide) (choices 2) [9,10] profile12_node24_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,17] (choices 2) [9,10] profile12_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node25
  · exact profile12_node29

def profile12_node33_cert : CutBound 5 := { lost := (rows 0 0 2 4 6), upper := (rows 7 22 13 11 25), lower := (rows 7 22 13 11 16), losses := [{ target := 1, region := (rows 1 0 12 8 28), good := (rows 21 20 29 29 16) },{ target := 2, region := (rows 1 2 0 9 29), good := (rows 27 18 25 27 16) }] }

theorem profile12_node33 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9,3] 3 profile12_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9,3] 3 profile12_node33_cert).mp (by decide +kernel))

def profile12_node32_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node32 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9] 3 (by decide) (choices 2) [3] profile12_node32_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20,9] (choices 2) [3] profile12_node32_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node33

def profile12_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node31 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] 3 (by decide) (choices 2) [9] profile12_node31_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,20] (choices 2) [9] profile12_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node32

def profile12_node35_cert : CutBound 5 := { lost := (rows 8 0 8 2 2), upper := (rows 7 26 7 13 29), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile12_node35 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 3 profile12_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,3] 3 profile12_node35_cert).mp (by decide +kernel))

def profile12_node37_cert : CutBound 5 := { lost := (rows 0 0 2 4 10), upper := (rows 7 26 13 11 21), lower := (rows 7 26 13 11 16), losses := [{ target := 1, region := (rows 1 0 12 8 29), good := (rows 21 28 29 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 11 26 9 11 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 18 21 19 16) }] }

theorem profile12_node37 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,3] 3 profile12_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,3] 3 profile12_node37_cert).mp (by decide +kernel))

def profile12_node38_cert : CutBound 5 := { lost := (rows 0 4 2 2 4), upper := (rows 7 26 13 13 19), lower := (rows 7 26 13 13 16), losses := [{ target := 1, region := (rows 1 0 13 13 16), good := (rows 13 28 13 13 16) },{ target := 2, region := (rows 1 14 0 8 29), good := (rows 19 26 27 27 16) }] }

theorem profile12_node38 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,5] 3 profile12_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9,5] 3 profile12_node38_cert).mp (by decide +kernel))

def profile12_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node36 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] 3 (by decide) (choices 2) [3,5] profile12_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24,9] (choices 2) [3,5] profile12_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node37
  · exact profile12_node38

def profile12_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node34 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24] 3 (by decide) (choices 2) [3,9] profile12_node34_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6,24] (choices 2) [3,9] profile12_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node35
  · exact profile12_node36

def profile12_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node1 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6] 3 (by decide) (choices 2) [5,9,12,17,20,24] profile12_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [6] (choices 2) [5,9,12,17,20,24] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node19
  · exact profile12_node24
  · exact profile12_node31
  · exact profile12_node34

def profile12_node42_cert : CutBound 5 := { lost := (rows 0 0 2 4 3), upper := (rows 19 7 13 11 28), lower := (rows 19 7 13 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 18 22 28 10 16) },{ target := 1, region := (rows 1 0 12 8 28), good := (rows 17 21 29 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 9 11 16) }] }

theorem profile12_node42 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,3] 3 profile12_node42_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,3] 3 profile12_node42_cert).mp (by decide +kernel))

def profile12_node44_cert : CutBound 5 := { lost := (rows 12 8 2 2 0), upper := (rows 19 7 13 13 26), lower := (rows 19 7 13 13 26), losses := [{ target := 1, region := (rows 1 0 15 15 16), good := (rows 29 13 13 13 28) },{ target := 2, region := (rows 17 2 0 8 16), good := (rows 19 3 9 9 27) },{ target := 3, region := (rows 17 14 4 0 16), good := (rows 19 7 7 7 19) }] }

theorem profile12_node44 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5,10] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5,10] 3 profile12_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5,10] 3 profile12_node44_cert).mp (by decide +kernel))

def profile12_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node43 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5] 3 (by decide) (choices 2) [10] profile12_node43_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,5] (choices 2) [10] profile12_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node44

def profile12_node45_cert : CutBound 5 := { lost := (rows 4 0 0 1 6), upper := (rows 19 7 13 14 25), lower := (rows 19 7 13 14 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 26 14 12 14 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 17 21 29 28 16) },{ target := 2, region := (rows 11 2 0 8 28), good := (rows 19 19 25 27 16) }] }

theorem profile12_node45 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,6] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,6] 3 profile12_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9,6] 3 profile12_node45_cert).mp (by decide +kernel))

def profile12_node41_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node41 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] 3 (by decide) (choices 2) [3,5,6] profile12_node41_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,9] (choices 2) [3,5,6] profile12_node41_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node42
  · exact profile12_node43
  · exact profile12_node45

def profile12_node47_cert : CutBound 5 := { lost := (rows 4 0 0 2 6), upper := (rows 19 7 14 13 25), lower := (rows 19 7 14 13 16), losses := [{ target := 1, region := (rows 1 0 4 10 27), good := (rows 25 29 28 29 16) },{ target := 2, region := (rows 7 2 0 8 28), good := (rows 19 19 27 25 16) }] }

theorem profile12_node47 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10,5] 3 profile12_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10,5] 3 profile12_node47_cert).mp (by decide +kernel))

def profile12_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node46 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] 3 (by decide) (choices 2) [5] profile12_node46_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5,10] (choices 2) [5] profile12_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node47

def profile12_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node40 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5] 3 (by decide) (choices 2) [9,10] profile12_node40_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,5] (choices 2) [9,10] profile12_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node41
  · exact profile12_node46

def profile12_node50_cert : CutBound 5 := { lost := (rows 4 1 0 2 6), upper := (rows 19 14 7 13 25), lower := (rows 19 14 7 13 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 18 14 6 14 16) },{ target := 1, region := (rows 1 0 4 12 28), good := (rows 17 28 29 29 16) },{ target := 2, region := (rows 7 2 0 8 26), good := (rows 19 27 19 25 16) }] }

theorem profile12_node50 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3,5] 3 profile12_node50_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3,5] 3 profile12_node50_cert).mp (by decide +kernel))

def profile12_node49_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node49 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] 3 (by decide) (choices 2) [5] profile12_node49_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,3] (choices 2) [5] profile12_node49_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node50

def profile12_node52_cert : CutBound 5 := { lost := (rows 0 1 2 4 2), upper := (rows 19 14 13 11 21), lower := (rows 19 14 13 11 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 18 14 14 10 16) },{ target := 1, region := (rows 1 0 12 8 28), good := (rows 17 28 29 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 10 9 11 16) }] }

theorem profile12_node52 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,3] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,3] 3 profile12_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,3] 3 profile12_node52_cert).mp (by decide +kernel))

def profile12_node53_cert : CutBound 5 := { lost := (rows 4 1 2 2 4), upper := (rows 19 14 13 13 19), lower := (rows 19 14 13 13 16), losses := [{ target := 0, region := (rows 0 14 4 8 16), good := (rows 18 14 14 14 16) },{ target := 1, region := (rows 1 0 13 13 16), good := (rows 29 12 13 13 16) },{ target := 2, region := (rows 3 2 0 8 19), good := (rows 19 27 25 25 16) }] }

theorem profile12_node53 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,5] 3 :=
  cut_bound_sound (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,5] 3 profile12_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9,5] 3 profile12_node53_cert).mp (by decide +kernel))

def profile12_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node51 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] 3 (by decide) (choices 2) [3,5] profile12_node51_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12,9] (choices 2) [3,5] profile12_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node52
  · exact profile12_node53

def profile12_node48_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node48 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12] 3 (by decide) (choices 2) [3,9] profile12_node48_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18,12] (choices 2) [3,9] profile12_node48_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node49
  · exact profile12_node51

def profile12_node39_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile12_node39 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18] 3 (by decide) (choices 2) [5,12] profile12_node39_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [18] (choices 2) [5,12] profile12_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node40
  · exact profile12_node48

def profile12_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile12_node0 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 3 := by
  apply routed_branch (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 3 (by decide) (choices 2) [6,18] profile12_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] (choices 2) [6,18] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node1
  · exact profile12_node39

theorem profile12 : Upper (D (n:=5) [35,34,34,34,33]) (R (n:=5) [35,34,34,34,33]) [] 3 := profile12_node0

def profile13_node4_cert : CutBound 5 := { lost := (rows 24 24 3 4 4), upper := (rows 7 7 28 25 26), lower := (rows 7 7 28 25 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 6 6 28 28 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 5 28 29 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 25 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 7 7 23 19 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 7 7 15 11 0) }] }

theorem profile13_node4 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,17] 3 profile13_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,17] 3 profile13_node4_cert).mp (by decide +kernel))

def profile13_node5_cert : CutBound 5 := { lost := (rows 24 24 3 4 4), upper := (rows 7 7 28 26 25), lower := (rows 7 7 28 26 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 6 6 28 30 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 5 28 28 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 24 26 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 7 7 23 19 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 7 7 15 11 0) }] }

theorem profile13_node5 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,18] 3 profile13_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24,18] 3 profile13_node5_cert).mp (by decide +kernel))

def profile13_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node3 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24] 3 (by decide) (choices 2) [17,18] profile13_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5,24] (choices 2) [17,18] profile13_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node4
  · exact profile13_node5

def profile13_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node2 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] 3 (by decide) (choices 2) [24] profile13_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] (choices 2) [24] profile13_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node3

def profile13_node8_cert : CutBound 5 := { lost := (rows 8 4 10 5 3), upper := (rows 7 11 21 26 28), lower := (rows 7 11 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 26), good := (rows 21 29 21 28 16) },{ target := 2, region := (rows 1 7 0 12 16), good := (rows 11 11 27 26 16) },{ target := 3, region := (rows 11 2 12 0 16), good := (rows 7 7 21 23 16) }] }

theorem profile13_node8 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 3 profile13_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 3 profile13_node8_cert).mp (by decide +kernel))

def profile13_node10_cert : CutBound 5 := { lost := (rows 24 16 8 3 5), upper := (rows 7 11 21 28 26), lower := (rows 7 11 21 28 26), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 26) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 9 29 28 24) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 17 24 26) },{ target := 3, region := (rows 19 2 28 0 16), good := (rows 7 7 21 21 23) },{ target := 4, region := (rows 13 26 4 8 0), good := (rows 7 11 7 15 11) }] }

theorem profile13_node10 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20,10] 3 profile13_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20,10] 3 profile13_node10_cert).mp (by decide +kernel))

def profile13_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node9 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] 3 (by decide) (choices 2) [10] profile13_node9_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] (choices 2) [10] profile13_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node10

def profile13_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node7 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17] 3 (by decide) (choices 2) [18,20] profile13_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17] (choices 2) [18,20] profile13_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node8
  · exact profile13_node9

def profile13_node12_cert : CutBound 5 := { lost := (rows 24 20 1 2 3), upper := (rows 7 11 22 25 28), lower := (rows 7 11 22 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 26), good := (rows 22 30 22 28 16) },{ target := 1, region := (rows 1 0 4 11 21), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 11 18 27 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 7 3 23 17 16) },{ target := 4, region := (rows 5 10 4 8 0), good := (rows 7 11 7 11 0) }] }

theorem profile13_node12 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,17] 3 profile13_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,17] 3 profile13_node12_cert).mp (by decide +kernel))

def profile13_node13_cert : CutBound 5 := { lost := (rows 24 16 0 3 6), upper := (rows 7 11 22 28 25), lower := (rows 7 11 22 28 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 10 30 28 16) },{ target := 1, region := (rows 1 0 4 13 19), good := (rows 29 25 28 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 18 24 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 7 3 23 21 16) },{ target := 4, region := (rows 13 10 4 8 0), good := (rows 7 11 7 15 0) }] }

theorem profile13_node13 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,20] 3 profile13_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18,20] 3 profile13_node13_cert).mp (by decide +kernel))

def profile13_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node11 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] 3 (by decide) (choices 2) [17,20] profile13_node11_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] (choices 2) [17,20] profile13_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node12
  · exact profile13_node13

def profile13_node15_cert : CutBound 5 := { lost := (rows 16 20 3 0 9), upper := (rows 7 11 28 25 22), lower := (rows 7 11 28 25 16), losses := [{ target := 0, region := (rows 0 2 14 8 19), good := (rows 22 30 28 28 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 13 28 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 11 26 27 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 20 17 16) },{ target := 4, region := (rows 5 14 4 8 0), good := (rows 7 11 15 11 0) }] }

theorem profile13_node15 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 3 profile13_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 3 profile13_node15_cert).mp (by decide +kernel))

def profile13_node17_cert : CutBound 5 := { lost := (rows 16 20 3 4 10), upper := (rows 7 11 28 26 21), lower := (rows 7 11 28 26 21), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 6 14 28 30 20) },{ target := 1, region := (rows 1 0 14 8 19), good := (rows 21 29 28 28 21) },{ target := 2, region := (rows 1 19 0 28 16), good := (rows 11 11 26 26 27) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 20 18 21) },{ target := 4, region := (rows 21 14 4 8 0), good := (rows 7 11 15 11 7) }] }

theorem profile13_node17 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18,5] 3 profile13_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18,5] 3 profile13_node17_cert).mp (by decide +kernel))

def profile13_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node16 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] 3 (by decide) (choices 2) [5] profile13_node16_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] (choices 2) [5] profile13_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node17

def profile13_node18_cert : CutBound 5 := { lost := (rows 16 16 3 3 12), upper := (rows 7 11 28 28 19), lower := (rows 7 11 28 28 16), losses := [{ target := 0, region := (rows 0 2 28 28 16), good := (rows 14 14 28 28 28) },{ target := 1, region := (rows 1 0 28 28 16), good := (rows 13 13 28 28 28) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 19 27 24 24 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 19 20 20 16) },{ target := 4, region := (rows 13 14 4 8 0), good := (rows 7 11 15 15 0) }] }

theorem profile13_node18 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 3 profile13_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 3 profile13_node18_cert).mp (by decide +kernel))

def profile13_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node14 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24] 3 (by decide) (choices 2) [17,18,20] profile13_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24] (choices 2) [17,18,20] profile13_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node15
  · exact profile13_node16
  · exact profile13_node18

def profile13_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node6 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9] 3 (by decide) (choices 2) [17,18,24] profile13_node6_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9] (choices 2) [17,18,24] profile13_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node7
  · exact profile13_node11
  · exact profile13_node14

def profile13_node21_cert : CutBound 5 := { lost := (rows 8 0 10 6 5), upper := (rows 7 14 21 25 26), lower := (rows 7 14 21 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 20 24 16) },{ target := 1, region := (rows 1 0 12 12 16), good := (rows 13 12 29 29 16) },{ target := 2, region := (rows 1 2 0 13 19), good := (rows 27 26 25 25 16) },{ target := 3, region := (rows 3 2 12 0 16), good := (rows 7 7 21 21 16) }] }

theorem profile13_node21 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,17] 3 profile13_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,17] 3 profile13_node21_cert).mp (by decide +kernel))

def profile13_node22_cert : CutBound 5 := { lost := (rows 24 1 8 5 4), upper := (rows 7 14 21 26 25), lower := (rows 7 14 21 26 16), losses := [{ target := 0, region := (rows 0 7 4 12 16), good := (rows 14 14 30 26 16) },{ target := 2, region := (rows 1 2 0 11 21), good := (rows 27 26 25 26 16) },{ target := 3, region := (rows 11 2 12 0 16), good := (rows 7 7 21 23 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 7 15 5 11 0) }] }

theorem profile13_node22 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,18] 3 profile13_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17,18] 3 profile13_node22_cert).mp (by decide +kernel))

def profile13_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node20 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17] 3 (by decide) (choices 2) [17,18] profile13_node20_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,17] (choices 2) [17,18] profile13_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node21
  · exact profile13_node22

def profile13_node24_cert : CutBound 5 := { lost := (rows 8 1 1 6 6), upper := (rows 7 14 22 25 25), lower := (rows 7 14 22 25 16), losses := [{ target := 0, region := (rows 0 10 12 8 16), good := (rows 6 14 22 30 16) },{ target := 1, region := (rows 1 0 4 9 25), good := (rows 29 28 20 25 16) },{ target := 2, region := (rows 1 2 0 9 25), good := (rows 27 26 18 25 16) },{ target := 3, region := (rows 7 2 4 0 16), good := (rows 7 7 23 17 16) }] }

theorem profile13_node24 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18,17] 3 profile13_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18,17] 3 profile13_node24_cert).mp (by decide +kernel))

def profile13_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node23 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18] 3 (by decide) (choices 2) [17] profile13_node23_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,18] (choices 2) [17] profile13_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node24

def profile13_node25_cert : CutBound 5 := { lost := (rows 24 17 0 4 12), upper := (rows 7 14 28 27 19), lower := (rows 7 14 28 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 6 14 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 24 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 7 6 4 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile13_node25 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,24] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,24] 3 profile13_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12,24] 3 profile13_node25_cert).mp (by decide +kernel))

def profile13_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node19 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] 3 (by decide) (choices 2) [17,18,24] profile13_node19_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] (choices 2) [17,18,24] profile13_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node20
  · exact profile13_node23
  · exact profile13_node25

def profile13_node28_cert : CutBound 5 := { lost := (rows 24 5 24 2 2), upper := (rows 7 26 7 25 28), lower := (rows 7 26 7 25 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 6 26 6 26 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 25 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 26 3 27 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 23 7 21 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 15 7 13 0) }] }

theorem profile13_node28 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,17] 3 profile13_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,17] 3 profile13_node28_cert).mp (by decide +kernel))

def profile13_node29_cert : CutBound 5 := { lost := (rows 24 5 24 2 2), upper := (rows 7 26 7 28 25), lower := (rows 7 26 7 28 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 6 26 6 30 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 28 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 26 3 26 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 23 7 21 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 7 15 7 13 0) }] }

theorem profile13_node29 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,20] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,20] 3 profile13_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3,20] 3 profile13_node29_cert).mp (by decide +kernel))

def profile13_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node27 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] 3 (by decide) (choices 2) [17,20] profile13_node27_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] (choices 2) [17,20] profile13_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node28
  · exact profile13_node29

def profile13_node31_cert : CutBound 5 := { lost := (rows 16 5 18 0 9), upper := (rows 7 26 13 25 22), lower := (rows 7 26 13 25 16), losses := [{ target := 0, region := (rows 0 14 4 8 21), good := (rows 22 26 30 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 28 13 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 26 11 27 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 21 17 16) },{ target := 4, region := (rows 3 2 14 8 0), good := (rows 7 15 13 13 0) }] }

theorem profile13_node31 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 3 profile13_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 3 profile13_node31_cert).mp (by decide +kernel))

def profile13_node32_cert : CutBound 5 := { lost := (rows 16 5 16 5 10), upper := (rows 7 26 13 26 21), lower := (rows 7 26 13 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 14 26 14 26 26) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 24 29 24 16) },{ target := 2, region := (rows 1 26 0 26 16), good := (rows 11 26 11 26 26) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 18 21 18 16) },{ target := 4, region := (rows 11 2 14 8 0), good := (rows 7 15 13 15 0) }] }

theorem profile13_node32 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 3 profile13_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 3 profile13_node32_cert).mp (by decide +kernel))

def profile13_node34_cert : CutBound 5 := { lost := (rows 16 5 18 2 12), upper := (rows 7 26 13 28 19), lower := (rows 7 26 13 28 19), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 6 26 14 30 18) },{ target := 1, region := (rows 1 0 21 26 16), good := (rows 13 28 13 28 29) },{ target := 2, region := (rows 1 14 0 8 21), good := (rows 19 26 27 26 19) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 21 20 19) },{ target := 4, region := (rows 19 2 14 8 0), good := (rows 7 15 13 13 7) }] }

theorem profile13_node34 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20,3] 3 profile13_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20,3] 3 profile13_node34_cert).mp (by decide +kernel))

def profile13_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node33 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] 3 (by decide) (choices 2) [3] profile13_node33_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] (choices 2) [3] profile13_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node34

def profile13_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node30 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9] 3 (by decide) (choices 2) [17,18,20] profile13_node30_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9] (choices 2) [17,18,20] profile13_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node31
  · exact profile13_node32
  · exact profile13_node33

def profile13_node35_cert : CutBound 5 := { lost := (rows 24 0 17 2 10), upper := (rows 7 26 14 29 21), lower := (rows 7 26 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 18 23 0 16) },{ target := 4, region := (rows 7 2 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile13_node35 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 3 profile13_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 3 profile13_node35_cert).mp (by decide +kernel))

def profile13_node37_cert : CutBound 5 := { lost := (rows 0 5 3 4 10), upper := (rows 7 26 28 11 21), lower := (rows 7 26 28 11 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 6 30 30 14 16) },{ target := 1, region := (rows 1 0 14 8 25), good := (rows 21 28 28 29 16) },{ target := 2, region := (rows 1 6 0 9 16), good := (rows 11 26 26 11 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 20 19 16) }] }

theorem profile13_node37 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,3] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,3] 3 profile13_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,3] 3 profile13_node37_cert).mp (by decide +kernel))

def profile13_node38_cert : CutBound 5 := { lost := (rows 0 5 3 2 12), upper := (rows 7 26 28 13 19), lower := (rows 7 26 28 13 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 6 30 30 14 16) },{ target := 1, region := (rows 1 0 6 9 16), good := (rows 13 28 28 13 16) },{ target := 2, region := (rows 1 14 0 8 25), good := (rows 19 26 26 27 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 20 21 16) }] }

theorem profile13_node38 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,5] 3 :=
  cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,5] 3 profile13_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24,5] 3 profile13_node38_cert).mp (by decide +kernel))

def profile13_node36_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node36 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] 3 (by decide) (choices 2) [3,5] profile13_node36_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] (choices 2) [3,5] profile13_node36_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node37
  · exact profile13_node38

def profile13_node26_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile13_node26 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24] 3 (by decide) (choices 2) [3,9,10,24] profile13_node26_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24] (choices 2) [3,9,10,24] profile13_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node27
  · exact profile13_node30
  · exact profile13_node35
  · exact profile13_node36

def profile13_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile13_node1 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6] 3 (by decide) (choices 2) [5,9,12,24] profile13_node1_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6] (choices 2) [5,9,12,24] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node6
  · exact profile13_node19
  · exact profile13_node26

def profile13_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 18 => (6,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (6,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 24 => (6,(fun i => match i.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile13_node0 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 3 := by
  apply routed_branch (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 3 (by decide) (choices 2) [6] profile13_node0_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] (choices 2) [6] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 3 := profile13_node0

#print axioms profile13
end Delivery.FiveVertexPositive10
