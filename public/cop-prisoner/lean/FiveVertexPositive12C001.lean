import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive12
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile23_node3_cert : CutBound 5 := { lost := (rows 0 0 8 3 0), upper := (rows 31 15 7 28 28), lower := (rows 31 15 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 7 7 0 16) }] }

theorem profile23_node3 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,3] 2 profile23_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,3] 2 profile23_node3_cert).mp (by decide +kernel))

def profile23_node4_cert : CutBound 5 := { lost := (rows 0 16 18 1 0), upper := (rows 31 15 13 30 22), lower := (rows 31 15 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 13 13 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile23_node4 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,9] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,9] 2 profile23_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,9] 2 profile23_node4_cert).mp (by decide +kernel))

def profile23_node5_cert : CutBound 5 := { lost := (rows 0 16 17 2 0), upper := (rows 31 15 14 29 21), lower := (rows 31 15 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 14 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 4, region := (rows 1 3 7 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile23_node5 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,10] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,10] 2 profile23_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,10] 2 profile23_node5_cert).mp (by decide +kernel))

def profile23_node6_cert : CutBound 5 := { lost := (rows 0 0 10 1 0), upper := (rows 31 15 21 14 30), lower := (rows 31 15 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 21 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 21 0 16) }] }

theorem profile23_node6 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,17] 2 profile23_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,17] 2 profile23_node6_cert).mp (by decide +kernel))

def profile23_node7_cert : CutBound 5 := { lost := (rows 0 0 9 2 0), upper := (rows 31 15 22 13 29), lower := (rows 31 15 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 22 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 22 0 16) }] }

theorem profile23_node7 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,18] 2 profile23_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,18] 2 profile23_node7_cert).mp (by decide +kernel))

def profile23_node8_cert : CutBound 5 := { lost := (rows 0 16 3 16 0), upper := (rows 31 15 28 15 23), lower := (rows 31 15 28 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 28 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile23_node8 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,24] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,24] 2 profile23_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13,24] 2 profile23_node8_cert).mp (by decide +kernel))

def profile23_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node2 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13] 2 (by decide) (choices 2) [3,9,10,17,18,24] profile23_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,13] (choices 2) [3,9,10,17,18,24] profile23_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile23_node3
  · exact profile23_node4
  · exact profile23_node5
  · exact profile23_node6
  · exact profile23_node7
  · exact profile23_node8

def profile23_node9_cert : CutBound 5 := { lost := (rows 0 8 16 16 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile23_node9 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,21] 2 profile23_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,21] 2 profile23_node9_cert).mp (by decide +kernel))

def profile23_node10_cert : CutBound 5 := { lost := (rows 0 1 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile23_node10 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,28] 2 profile23_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30,28] 2 profile23_node10_cert).mp (by decide +kernel))

def profile23_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile23_node1 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile23_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [30] (choices 3) [13,21,28] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile23_node2
  · exact profile23_node9
  · exact profile23_node10

def profile23_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [] 2 (by decide) (choices 4) [30] profile23_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [] (choices 4) [30] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=5) [66,50,35,35,18]) (R (n:=5) [66,50,35,35,18]) [] 2 := profile23_node0

def profile24_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile24_node2 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,13] 2 profile24_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,13] 2 profile24_node2_cert).mp (by decide +kernel))

def profile24_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 14 14 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile24_node3 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,21] 2 profile24_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,21] 2 profile24_node3_cert).mp (by decide +kernel))

def profile24_node4_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile24_node4 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,28] 2 profile24_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30,28] 2 profile24_node4_cert).mp (by decide +kernel))

def profile24_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile24_node1 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile24_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [30] (choices 3) [13,21,28] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile24_node2
  · exact profile24_node3
  · exact profile24_node4

def profile24_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [] 2 (by decide) (choices 4) [30] profile24_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [] (choices 4) [30] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=5) [65,51,35,35,18]) (R (n:=5) [65,51,35,35,18]) [] 2 := profile24_node0

def profile25_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 29 29 29), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile25_node2 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,13] 2 profile25_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,13] 2 profile25_node2_cert).mp (by decide +kernel))

def profile25_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 13 13 29), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile25_node3 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,21] 2 profile25_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,21] 2 profile25_node3_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 13 13 29), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile25_node4 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,28] 2 profile25_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30,28] 2 profile25_node4_cert).mp (by decide +kernel))

def profile25_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node1 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile25_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [30] (choices 3) [13,21,28] profile25_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node2
  · exact profile25_node3
  · exact profile25_node4

def profile25_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node0 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [] 2 (by decide) (choices 4) [30] profile25_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [] (choices 4) [30] profile25_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node1

theorem profile25 : Upper (D (n:=5) [66,49,36,35,18]) (R (n:=5) [66,49,36,35,18]) [] 2 := profile25_node0

def profile26_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile26_node2 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,13] 2 profile26_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,13] 2 profile26_node2_cert).mp (by decide +kernel))

def profile26_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 14 14 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile26_node3 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,21] 2 profile26_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,21] 2 profile26_node3_cert).mp (by decide +kernel))

def profile26_node4_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile26_node4 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,28] 2 profile26_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30,28] 2 profile26_node4_cert).mp (by decide +kernel))

def profile26_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile26_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [30] (choices 3) [13,21,28] profile26_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node2
  · exact profile26_node3
  · exact profile26_node4

def profile26_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node0 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [] 2 (by decide) (choices 4) [30] profile26_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [] (choices 4) [30] profile26_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node1

theorem profile26 : Upper (D (n:=5) [65,50,36,35,18]) (R (n:=5) [65,50,36,35,18]) [] 2 := profile26_node0

def profile27_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 27 15 25 17), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile27_node3 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,11] 2 profile27_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,11] 2 profile27_node3_cert).mp (by decide +kernel))

def profile27_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 27 23 9 25), lower := (rows 15 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile27_node4 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,19] 2 profile27_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,19] 2 profile27_node4_cert).mp (by decide +kernel))

def profile27_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 27 29 11 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) }] }

theorem profile27_node5 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,25] 2 profile27_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25,25] 2 profile27_node5_cert).mp (by decide +kernel))

def profile27_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node2 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25] 2 (by decide) (choices 3) [11,19,25] profile27_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14,25] (choices 3) [11,19,25] profile27_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node3
  · exact profile27_node4
  · exact profile27_node5

def profile27_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14] 2 (by decide) (choices 3) [25] profile27_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [14] (choices 3) [25] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node2

def profile27_node7_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 15 11 27), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile27_node7 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22,25] 2 profile27_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22,25] 2 profile27_node7_cert).mp (by decide +kernel))

def profile27_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node6 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22] 2 (by decide) (choices 3) [25] profile27_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [22] (choices 3) [25] profile27_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node7

def profile27_node10_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 15 15 25 17), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile27_node10 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,11] 2 profile27_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,11] 2 profile27_node10_cert).mp (by decide +kernel))

def profile27_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 15 23 9 25), lower := (rows 27 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile27_node11 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,19] 2 profile27_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,19] 2 profile27_node11_cert).mp (by decide +kernel))

def profile27_node12_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 15 29 11 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) }] }

theorem profile27_node12 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,25] 2 profile27_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13,25] 2 profile27_node12_cert).mp (by decide +kernel))

def profile27_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node9 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13] 2 (by decide) (choices 3) [11,19,25] profile27_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,13] (choices 3) [11,19,25] profile27_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node10
  · exact profile27_node11
  · exact profile27_node12

def profile27_node13_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 15 11 27), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile27_node13 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,21] 2 profile27_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,21] 2 profile27_node13_cert).mp (by decide +kernel))

def profile27_node14_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile27_node14 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,25] 2 profile27_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26,25] 2 profile27_node14_cert).mp (by decide +kernel))

def profile27_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node8 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26] 2 (by decide) (choices 3) [13,21,25] profile27_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [26] (choices 3) [13,21,25] profile27_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node9
  · exact profile27_node13
  · exact profile27_node14

def profile27_node16_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile27_node16 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28,25] 2 profile27_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28,25] 2 profile27_node16_cert).mp (by decide +kernel))

def profile27_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node15 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28] 2 (by decide) (choices 3) [25] profile27_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [28] (choices 3) [25] profile27_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node16

def profile27_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [] 2 (by decide) (choices 3) [14,22,26,28] profile27_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [] (choices 3) [14,22,26,28] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile27_node1
  · exact profile27_node6
  · exact profile27_node8
  · exact profile27_node15

theorem profile27 : Upper (D (n:=5) [52,50,49,35,18]) (R (n:=5) [52,50,49,35,18]) [] 2 := profile27_node0

def profile28_node3_cert : CutBound 5 := { lost := (rows 16 0 16 0 0), upper := (rows 15 27 15 27 19), lower := (rows 15 27 15 8 16), losses := [{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile28_node3 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,11] 2 profile28_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,11] 2 profile28_node3_cert).mp (by decide +kernel))

def profile28_node4_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 15 27 23 11 27), lower := (rows 15 27 23 8 16), losses := [{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile28_node4 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,19] 2 profile28_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,19] 2 profile28_node4_cert).mp (by decide +kernel))

def profile28_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 27 29 11 19), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) }] }

theorem profile28_node5 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,25] 2 profile28_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,25] 2 profile28_node5_cert).mp (by decide +kernel))

def profile28_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 27 30 11 19), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) }] }

theorem profile28_node6 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,26] 2 profile28_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25,26] 2 profile28_node6_cert).mp (by decide +kernel))

def profile28_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node2 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25] 2 (by decide) (choices 3) [11,19,25,26] profile28_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14,25] (choices 3) [11,19,25,26] profile28_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node3
  · exact profile28_node4
  · exact profile28_node5
  · exact profile28_node6

def profile28_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node1 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14] 2 (by decide) (choices 3) [25] profile28_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [14] (choices 3) [25] profile28_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node2

def profile28_node8_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 15 11 27), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile28_node8 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22,25] 2 profile28_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22,25] 2 profile28_node8_cert).mp (by decide +kernel))

def profile28_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node7 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22] 2 (by decide) (choices 3) [25] profile28_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [22] (choices 3) [25] profile28_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node8

def profile28_node11_cert : CutBound 5 := { lost := (rows 0 16 16 0 0), upper := (rows 27 15 15 27 19), lower := (rows 27 15 15 8 16), losses := [{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile28_node11 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,11] 2 profile28_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,11] 2 profile28_node11_cert).mp (by decide +kernel))

def profile28_node12_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 27 15 23 11 27), lower := (rows 27 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile28_node12 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,19] 2 profile28_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,19] 2 profile28_node12_cert).mp (by decide +kernel))

def profile28_node13_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 15 29 11 19), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) }] }

theorem profile28_node13 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,25] 2 profile28_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,25] 2 profile28_node13_cert).mp (by decide +kernel))

def profile28_node14_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 15 30 11 19), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) }] }

theorem profile28_node14 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,26] 2 profile28_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13,26] 2 profile28_node14_cert).mp (by decide +kernel))

def profile28_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node10 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13] 2 (by decide) (choices 3) [11,19,25,26] profile28_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,13] (choices 3) [11,19,25,26] profile28_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node11
  · exact profile28_node12
  · exact profile28_node13
  · exact profile28_node14

def profile28_node15_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 15 11 27), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile28_node15 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,21] 2 profile28_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,21] 2 profile28_node15_cert).mp (by decide +kernel))

def profile28_node16_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile28_node16 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,25] 2 profile28_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,25] 2 profile28_node16_cert).mp (by decide +kernel))

def profile28_node17_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 30 15 11 27), lower := (rows 27 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile28_node17 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,28] 2 profile28_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26,28] 2 profile28_node17_cert).mp (by decide +kernel))

def profile28_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node9 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile28_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [26] (choices 3) [13,21,25,28] profile28_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node10
  · exact profile28_node15
  · exact profile28_node16
  · exact profile28_node17

def profile28_node19_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile28_node19 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28,25] 2 profile28_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28,25] 2 profile28_node19_cert).mp (by decide +kernel))

def profile28_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node18 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28] 2 (by decide) (choices 3) [25] profile28_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [28] (choices 3) [25] profile28_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node19

def profile28_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [] 2 (by decide) (choices 3) [14,22,26,28] profile28_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [] (choices 3) [14,22,26,28] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node1
  · exact profile28_node7
  · exact profile28_node9
  · exact profile28_node18

theorem profile28 : Upper (D (n:=5) [51,51,49,35,18]) (R (n:=5) [51,51,49,35,18]) [] 2 := profile28_node0

def profile29_node2_cert : CutBound 5 := { lost := (rows 16 16 0 4 0), upper := (rows 15 15 31 27 27), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile29_node2 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,13] 2 profile29_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,13] 2 profile29_node2_cert).mp (by decide +kernel))

def profile29_node4_cert : CutBound 5 := { lost := (rows 16 0 16 6 0), upper := (rows 15 23 15 25 25), lower := (rows 15 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile29_node4 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,11] 2 profile29_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,11] 2 profile29_node4_cert).mp (by decide +kernel))

def profile29_node5_cert : CutBound 5 := { lost := (rows 16 8 0 20 0), upper := (rows 15 23 29 11 27), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile29_node5 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,25] 2 profile29_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,25] 2 profile29_node5_cert).mp (by decide +kernel))

def profile29_node6_cert : CutBound 5 := { lost := (rows 16 0 0 22 0), upper := (rows 15 23 30 9 25), lower := (rows 15 23 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node6 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,26] 2 profile29_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21,26] 2 profile29_node6_cert).mp (by decide +kernel))

def profile29_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node3 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21] 2 (by decide) (choices 3) [11,25,26] profile29_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,21] (choices 3) [11,25,26] profile29_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node4
  · exact profile29_node5
  · exact profile29_node6

def profile29_node8_cert : CutBound 5 := { lost := (rows 16 0 16 2 0), upper := (rows 15 27 15 29 21), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node8 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,11] 2 profile29_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,11] 2 profile29_node8_cert).mp (by decide +kernel))

def profile29_node9_cert : CutBound 5 := { lost := (rows 16 0 8 18 0), upper := (rows 15 27 23 13 29), lower := (rows 15 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 1 2 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile29_node9 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,19] 2 profile29_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,19] 2 profile29_node9_cert).mp (by decide +kernel))

def profile29_node10_cert : CutBound 5 := { lost := (rows 0 4 2 16 0), upper := (rows 15 27 29 15 23), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 27 27 8 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile29_node10 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,25] 2 profile29_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,25] 2 profile29_node10_cert).mp (by decide +kernel))

def profile29_node11_cert : CutBound 5 := { lost := (rows 16 0 1 18 0), upper := (rows 15 27 30 13 21), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile29_node11 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,26] 2 profile29_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25,26] 2 profile29_node11_cert).mp (by decide +kernel))

def profile29_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node7 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25] 2 (by decide) (choices 3) [11,19,25,26] profile29_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,25] (choices 3) [11,19,25,26] profile29_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node8
  · exact profile29_node9
  · exact profile29_node10
  · exact profile29_node11

def profile29_node13_cert : CutBound 5 := { lost := (rows 16 0 16 6 0), upper := (rows 15 30 15 25 17), lower := (rows 15 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node13 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,11] 2 profile29_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,11] 2 profile29_node13_cert).mp (by decide +kernel))

def profile29_node14_cert : CutBound 5 := { lost := (rows 16 0 0 22 0), upper := (rows 15 30 23 9 25), lower := (rows 15 30 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node14 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,19] 2 profile29_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,19] 2 profile29_node14_cert).mp (by decide +kernel))

def profile29_node15_cert : CutBound 5 := { lost := (rows 16 1 0 20 0), upper := (rows 15 30 29 11 19), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile29_node15 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,25] 2 profile29_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28,25] 2 profile29_node15_cert).mp (by decide +kernel))

def profile29_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node12 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28] 2 (by decide) (choices 3) [11,19,25] profile29_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14,28] (choices 3) [11,19,25] profile29_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node13
  · exact profile29_node14
  · exact profile29_node15

def profile29_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node1 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14] 2 (by decide) (choices 3) [13,21,25,28] profile29_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [14] (choices 3) [13,21,25,28] profile29_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node2
  · exact profile29_node3
  · exact profile29_node7
  · exact profile29_node12

def profile29_node18_cert : CutBound 5 := { lost := (rows 0 16 16 6 0), upper := (rows 23 15 15 25 25), lower := (rows 23 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile29_node18 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,11] 2 profile29_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,11] 2 profile29_node18_cert).mp (by decide +kernel))

def profile29_node19_cert : CutBound 5 := { lost := (rows 0 16 0 20 0), upper := (rows 23 15 29 11 27), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node19 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,25] 2 profile29_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,25] 2 profile29_node19_cert).mp (by decide +kernel))

def profile29_node20_cert : CutBound 5 := { lost := (rows 8 0 0 6 0), upper := (rows 23 15 30 9 25), lower := (rows 23 15 30 8 16), losses := [{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile29_node20 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,26] 2 profile29_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13,26] 2 profile29_node20_cert).mp (by decide +kernel))

def profile29_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node17 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13] 2 (by decide) (choices 3) [11,25,26] profile29_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,13] (choices 3) [11,25,26] profile29_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node18
  · exact profile29_node19
  · exact profile29_node20

def profile29_node22_cert : CutBound 5 := { lost := (rows 0 0 16 18 0), upper := (rows 23 27 15 13 29), lower := (rows 23 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node22 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25,11] 2 profile29_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25,11] 2 profile29_node22_cert).mp (by decide +kernel))

def profile29_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node21 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25] 2 (by decide) (choices 3) [11] profile29_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,25] (choices 3) [11] profile29_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node22

def profile29_node23_cert : CutBound 5 := { lost := (rows 8 0 16 20 0), upper := (rows 23 30 15 11 27), lower := (rows 23 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile29_node23 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,28] 2 profile29_node23_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22,28] 2 profile29_node23_cert).mp (by decide +kernel))

def profile29_node16_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node16 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22] 2 (by decide) (choices 3) [13,25,28] profile29_node16_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [22] (choices 3) [13,25,28] profile29_node16_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node17
  · exact profile29_node21
  · exact profile29_node23

def profile29_node26_cert : CutBound 5 := { lost := (rows 0 16 16 2 0), upper := (rows 27 15 15 29 21), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node26 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,11] 2 profile29_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,11] 2 profile29_node26_cert).mp (by decide +kernel))

def profile29_node27_cert : CutBound 5 := { lost := (rows 0 16 8 18 0), upper := (rows 27 15 23 13 29), lower := (rows 27 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile29_node27 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,19] 2 profile29_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,19] 2 profile29_node27_cert).mp (by decide +kernel))

def profile29_node28_cert : CutBound 5 := { lost := (rows 0 16 2 16 0), upper := (rows 27 15 29 15 23), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile29_node28 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,25] 2 profile29_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,25] 2 profile29_node28_cert).mp (by decide +kernel))

def profile29_node29_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 15 30 13 21), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 11 27 8 16) }] }

theorem profile29_node29 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,26] 2 profile29_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13,26] 2 profile29_node29_cert).mp (by decide +kernel))

def profile29_node25_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node25 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13] 2 (by decide) (choices 3) [11,19,25,26] profile29_node25_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,13] (choices 3) [11,19,25,26] profile29_node25_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node26
  · exact profile29_node27
  · exact profile29_node28
  · exact profile29_node29

def profile29_node31_cert : CutBound 5 := { lost := (rows 0 0 16 18 0), upper := (rows 27 23 15 13 29), lower := (rows 27 23 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile29_node31 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21,11] 2 profile29_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21,11] 2 profile29_node31_cert).mp (by decide +kernel))

def profile29_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node30 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21] 2 (by decide) (choices 3) [11] profile29_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,21] (choices 3) [11] profile29_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node31

def profile29_node32_cert : CutBound 5 := { lost := (rows 4 4 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile29_node32 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,25] 2 profile29_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,25] 2 profile29_node32_cert).mp (by decide +kernel))

def profile29_node33_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 27 30 15 15 31), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile29_node33 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,28] 2 profile29_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26,28] 2 profile29_node33_cert).mp (by decide +kernel))

def profile29_node24_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node24 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26] 2 (by decide) (choices 3) [13,21,25,28] profile29_node24_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [26] (choices 3) [13,21,25,28] profile29_node24_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node25
  · exact profile29_node30
  · exact profile29_node32
  · exact profile29_node33

def profile29_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile29_node0 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [] 2 (by decide) (choices 3) [14,22,26] profile29_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [] (choices 3) [14,22,26] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node1
  · exact profile29_node16
  · exact profile29_node24

theorem profile29 : Upper (D (n:=5) [51,50,50,35,18]) (R (n:=5) [51,50,50,35,18]) [] 2 := profile29_node0

def profile30_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 27 15 25 25), lower := (rows 15 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile30_node3 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,11] 2 profile30_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,11] 2 profile30_node3_cert).mp (by decide +kernel))

def profile30_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 15 27 29 11 27), lower := (rows 15 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) }] }

theorem profile30_node4 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,25] 2 profile30_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,25] 2 profile30_node4_cert).mp (by decide +kernel))

def profile30_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 27 30 9 25), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) }] }

theorem profile30_node5 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,26] 2 profile30_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25,26] 2 profile30_node5_cert).mp (by decide +kernel))

def profile30_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node2 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25] 2 (by decide) (choices 3) [11,25,26] profile30_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14,25] (choices 3) [11,25,26] profile30_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node3
  · exact profile30_node4
  · exact profile30_node5

def profile30_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node1 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14] 2 (by decide) (choices 3) [25] profile30_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [14] (choices 3) [25] profile30_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile30_node2

def profile30_node8_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 15 15 25 25), lower := (rows 27 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 25 29 29 8 16) }] }

theorem profile30_node8 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,11] 2 profile30_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,11] 2 profile30_node8_cert).mp (by decide +kernel))

def profile30_node9_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 27 15 29 11 27), lower := (rows 27 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) }] }

theorem profile30_node9 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,25] 2 profile30_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,25] 2 profile30_node9_cert).mp (by decide +kernel))

def profile30_node10_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 27 15 30 9 25), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) }] }

theorem profile30_node10 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,26] 2 profile30_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13,26] 2 profile30_node10_cert).mp (by decide +kernel))

def profile30_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node7 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13] 2 (by decide) (choices 3) [11,25,26] profile30_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,13] (choices 3) [11,25,26] profile30_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node8
  · exact profile30_node9
  · exact profile30_node10

def profile30_node11_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile30_node11 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,25] 2 profile30_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,25] 2 profile30_node11_cert).mp (by decide +kernel))

def profile30_node12_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 30 15 11 27), lower := (rows 27 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile30_node12 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,28] 2 profile30_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26,28] 2 profile30_node12_cert).mp (by decide +kernel))

def profile30_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node6 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26] 2 (by decide) (choices 3) [13,25,28] profile30_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [26] (choices 3) [13,25,28] profile30_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node7
  · exact profile30_node11
  · exact profile30_node12

def profile30_node14_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 29 27 15 11 27), lower := (rows 29 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 6 10 0), good := (rows 13 15 4 8 0) }] }

theorem profile30_node14 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28,25] 2 profile30_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28,25] 2 profile30_node14_cert).mp (by decide +kernel))

def profile30_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node13 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28] 2 (by decide) (choices 3) [25] profile30_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [28] (choices 3) [25] profile30_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile30_node14

def profile30_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node0 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [] 2 (by decide) (choices 3) [14,26,28] profile30_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [] (choices 3) [14,26,28] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile30_node1
  · exact profile30_node6
  · exact profile30_node13

theorem profile30 : Upper (D (n:=5) [51,50,49,36,18]) (R (n:=5) [51,50,49,36,18]) [] 2 := profile30_node0

def profile31_node2_cert : CutBound 5 := { lost := (rows 16 16 0 4 0), upper := (rows 15 15 31 27 27), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile31_node2 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,13] 2 profile31_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,13] 2 profile31_node2_cert).mp (by decide +kernel))

def profile31_node4_cert : CutBound 5 := { lost := (rows 16 0 16 3 0), upper := (rows 15 27 15 28 28), lower := (rows 15 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile31_node4 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,11] 2 profile31_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,11] 2 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : CutBound 5 := { lost := (rows 0 4 2 1 0), upper := (rows 15 27 29 14 30), lower := (rows 15 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 13 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 11 27 27 8 16) }] }

theorem profile31_node5 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,25] 2 profile31_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,25] 2 profile31_node5_cert).mp (by decide +kernel))

def profile31_node6_cert : CutBound 5 := { lost := (rows 16 0 1 18 0), upper := (rows 15 27 30 13 29), lower := (rows 15 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile31_node6 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,26] 2 profile31_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25,26] 2 profile31_node6_cert).mp (by decide +kernel))

def profile31_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node3 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25] 2 (by decide) (choices 3) [11,25,26] profile31_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,25] (choices 3) [11,25,26] profile31_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node4
  · exact profile31_node5
  · exact profile31_node6

def profile31_node8_cert : CutBound 5 := { lost := (rows 16 0 16 6 0), upper := (rows 15 30 15 25 25), lower := (rows 15 30 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile31_node8 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,11] 2 profile31_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,11] 2 profile31_node8_cert).mp (by decide +kernel))

def profile31_node9_cert : CutBound 5 := { lost := (rows 16 1 0 20 0), upper := (rows 15 30 29 11 27), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile31_node9 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,25] 2 profile31_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,25] 2 profile31_node9_cert).mp (by decide +kernel))

def profile31_node10_cert : CutBound 5 := { lost := (rows 0 1 1 2 0), upper := (rows 15 30 30 9 25), lower := (rows 15 30 30 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 14 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) }] }

theorem profile31_node10 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,26] 2 profile31_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28,26] 2 profile31_node10_cert).mp (by decide +kernel))

def profile31_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node7 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28] 2 (by decide) (choices 3) [11,25,26] profile31_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14,28] (choices 3) [11,25,26] profile31_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node8
  · exact profile31_node9
  · exact profile31_node10

def profile31_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node1 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14] 2 (by decide) (choices 3) [13,25,28] profile31_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [14] (choices 3) [13,25,28] profile31_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node2
  · exact profile31_node3
  · exact profile31_node7

def profile31_node13_cert : CutBound 5 := { lost := (rows 0 16 16 3 0), upper := (rows 27 15 15 28 28), lower := (rows 27 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 14 22), good := (rows 26 30 30 8 16) },{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile31_node13 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,11] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,11] 2 profile31_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,11] 2 profile31_node13_cert).mp (by decide +kernel))

def profile31_node14_cert : CutBound 5 := { lost := (rows 0 16 2 17 0), upper := (rows 27 15 29 14 30), lower := (rows 27 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 10 18), good := (rows 26 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile31_node14 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,25] 2 profile31_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,25] 2 profile31_node14_cert).mp (by decide +kernel))

def profile31_node15_cert : CutBound 5 := { lost := (rows 4 0 1 2 0), upper := (rows 27 15 30 13 29), lower := (rows 27 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 10 18), good := (rows 25 29 28 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 11 27 8 16) }] }

theorem profile31_node15 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,26] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,26] 2 profile31_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13,26] 2 profile31_node15_cert).mp (by decide +kernel))

def profile31_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node12 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13] 2 (by decide) (choices 3) [11,25,26] profile31_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,13] (choices 3) [11,25,26] profile31_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node13
  · exact profile31_node14
  · exact profile31_node15

def profile31_node16_cert : CutBound 5 := { lost := (rows 4 4 16 16 0), upper := (rows 27 27 15 15 31), lower := (rows 27 27 4 8 16), losses := [{ target := 2, region := (rows 3 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile31_node16 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,25] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,25] 2 profile31_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,25] 2 profile31_node16_cert).mp (by decide +kernel))

def profile31_node17_cert : CutBound 5 := { lost := (rows 4 0 16 16 0), upper := (rows 27 30 15 15 31), lower := (rows 27 30 4 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile31_node17 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,28] 2 :=
  cut_bound_sound (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,28] 2 profile31_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26,28] 2 profile31_node17_cert).mp (by decide +kernel))

def profile31_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node11 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26] 2 (by decide) (choices 3) [13,25,28] profile31_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [26] (choices 3) [13,25,28] profile31_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile31_node12
  · exact profile31_node16
  · exact profile31_node17

def profile31_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile31_node0 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [] 2 (by decide) (choices 3) [14,26] profile31_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [] (choices 3) [14,26] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile31_node1
  · exact profile31_node11

theorem profile31 : Upper (D (n:=5) [50,50,50,36,18]) (R (n:=5) [50,50,50,36,18]) [] 2 := profile31_node0

def profile32_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 23 27 19), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile32_node2 : Upper (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30,21] 2 profile32_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30,21] 2 profile32_node2_cert).mp (by decide +kernel))

def profile32_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node1 : Upper (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30] 2 (by decide) (choices 3) [21] profile32_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [30] (choices 3) [21] profile32_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node2

def profile32_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node0 : Upper (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [] 2 (by decide) (choices 4) [30] profile32_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [] (choices 4) [30] profile32_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node1

theorem profile32 : Upper (D (n:=5) [68,50,34,33,19]) (R (n:=5) [68,50,34,33,19]) [] 2 := profile32_node0

def profile33_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 23 27 19), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile33_node2 : Upper (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30,21] 2 profile33_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30,21] 2 profile33_node2_cert).mp (by decide +kernel))

def profile33_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node1 : Upper (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30] 2 (by decide) (choices 3) [21] profile33_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [30] (choices 3) [21] profile33_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node2

def profile33_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node0 : Upper (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [] 2 (by decide) (choices 4) [30] profile33_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [] (choices 4) [30] profile33_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node1

theorem profile33 : Upper (D (n:=5) [67,51,34,33,19]) (R (n:=5) [67,51,34,33,19]) [] 2 := profile33_node0

def profile34_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 23 27 19), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile34_node2 : Upper (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30,21] 2 profile34_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30,21] 2 profile34_node2_cert).mp (by decide +kernel))

def profile34_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node1 : Upper (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30] 2 (by decide) (choices 3) [21] profile34_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [30] (choices 3) [21] profile34_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node2

def profile34_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node0 : Upper (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [] 2 (by decide) (choices 4) [30] profile34_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [] (choices 4) [30] profile34_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node1

theorem profile34 : Upper (D (n:=5) [66,52,34,33,19]) (R (n:=5) [66,52,34,33,19]) [] 2 := profile34_node0

def profile35_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 23 7 29 21), lower := (rows 31 23 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile35_node3 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,3] 2 profile35_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,3] 2 profile35_node3_cert).mp (by decide +kernel))

def profile35_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 23 21 15 23), lower := (rows 31 23 21 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 21 21 8 16) }] }

theorem profile35_node4 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,17] 2 profile35_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,17] 2 profile35_node4_cert).mp (by decide +kernel))

def profile35_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 23 22 13 21), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile35_node5 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,18] 2 profile35_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21,18] 2 profile35_node5_cert).mp (by decide +kernel))

def profile35_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node2 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21] 2 (by decide) (choices 2) [3,17,18] profile35_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30,21] (choices 2) [3,17,18] profile35_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile35_node3
  · exact profile35_node4
  · exact profile35_node5

def profile35_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node1 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30] 2 (by decide) (choices 3) [21] profile35_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [30] (choices 3) [21] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node2

def profile35_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node0 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [] 2 (by decide) (choices 4) [30] profile35_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [] (choices 4) [30] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=5) [67,50,35,33,19]) (R (n:=5) [67,50,35,33,19]) [] 2 := profile35_node0

def profile36_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 23 7 30 22), lower := (rows 31 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile36_node3 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,3] 2 profile36_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,3] 2 profile36_node3_cert).mp (by decide +kernel))

def profile36_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 23 21 14 22), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile36_node4 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,17] 2 profile36_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,17] 2 profile36_node4_cert).mp (by decide +kernel))

def profile36_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 23 22 15 23), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile36_node5 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,18] 2 profile36_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21,18] 2 profile36_node5_cert).mp (by decide +kernel))

def profile36_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node2 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21] 2 (by decide) (choices 2) [3,17,18] profile36_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30,21] (choices 2) [3,17,18] profile36_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile36_node3
  · exact profile36_node4
  · exact profile36_node5

def profile36_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30] 2 (by decide) (choices 3) [21] profile36_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [30] (choices 3) [21] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node2

def profile36_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node0 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [] 2 (by decide) (choices 4) [30] profile36_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [] (choices 4) [30] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node1

theorem profile36 : Upper (D (n:=5) [66,51,35,33,19]) (R (n:=5) [66,51,35,33,19]) [] 2 := profile36_node0

def profile37_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 23 7 28 20), lower := (rows 31 23 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile37_node3 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,3] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,3] 2 profile37_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,3] 2 profile37_node3_cert).mp (by decide +kernel))

def profile37_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 23 21 14 22), lower := (rows 31 23 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile37_node4 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,17] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,17] 2 profile37_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,17] 2 profile37_node4_cert).mp (by decide +kernel))

def profile37_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 23 22 13 21), lower := (rows 31 23 22 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 22 22 8 16) }] }

theorem profile37_node5 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,18] 2 :=
  cut_bound_sound (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,18] 2 profile37_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21,18] 2 profile37_node5_cert).mp (by decide +kernel))

def profile37_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node2 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21] 2 (by decide) (choices 2) [3,17,18] profile37_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30,21] (choices 2) [3,17,18] profile37_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile37_node3
  · exact profile37_node4
  · exact profile37_node5

def profile37_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30] 2 (by decide) (choices 3) [21] profile37_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [30] (choices 3) [21] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node2

def profile37_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node0 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [] 2 (by decide) (choices 4) [30] profile37_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [] (choices 4) [30] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=5) [66,50,36,33,19]) (R (n:=5) [66,50,36,33,19]) [] 2 := profile37_node0

def profile38_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile38_node2 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14,21] 2 profile38_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14,21] 2 profile38_node2_cert).mp (by decide +kernel))

def profile38_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14] 2 (by decide) (choices 3) [21] profile38_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [14] (choices 3) [21] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node2

def profile38_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile38_node4 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,13] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,13] 2 profile38_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,13] 2 profile38_node4_cert).mp (by decide +kernel))

def profile38_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile38_node5 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,21] 2 profile38_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,21] 2 profile38_node5_cert).mp (by decide +kernel))

def profile38_node7_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 23 13 21), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) }] }

theorem profile38_node7 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25,19] 2 profile38_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25,19] 2 profile38_node7_cert).mp (by decide +kernel))

def profile38_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node6 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25] 2 (by decide) (choices 3) [19] profile38_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22,25] (choices 3) [19] profile38_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node7

def profile38_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node3 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22] 2 (by decide) (choices 3) [13,21,25] profile38_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [22] (choices 3) [13,21,25] profile38_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node4
  · exact profile38_node5
  · exact profile38_node6

def profile38_node10_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 23 13 21), lower := (rows 27 23 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 14 22), good := (rows 25 29 29 8 16) }] }

theorem profile38_node10 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21,19] 2 profile38_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21,19] 2 profile38_node10_cert).mp (by decide +kernel))

def profile38_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node9 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21] 2 (by decide) (choices 3) [19] profile38_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26,21] (choices 3) [19] profile38_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node10

def profile38_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node8 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26] 2 (by decide) (choices 3) [21] profile38_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [26] (choices 3) [21] profile38_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node9

def profile38_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile38_node0 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [] 2 (by decide) (choices 3) [14,22,26] profile38_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [] (choices 3) [14,22,26] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node1
  · exact profile38_node3
  · exact profile38_node8

theorem profile38 : Upper (D (n:=5) [52,50,50,33,19]) (R (n:=5) [52,50,50,33,19]) [] 2 := profile38_node0

#print axioms profile38
end Delivery.FiveVertexPositive12
