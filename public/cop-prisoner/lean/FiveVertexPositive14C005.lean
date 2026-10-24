import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile123_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile123_node2 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,21] 2 profile123_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,21] 2 profile123_node2_cert).mp (by decide +kernel))

def profile123_node5_cert : CutBound 5 := { lost := (rows 8 4 8 4 0), upper := (rows 23 27 23 27 28), lower := (rows 23 27 23 27 16), losses := [{ target := 2, region := (rows 1 15 0 15 16), good := (rows 27 27 27 27 16) },{ target := 3, region := (rows 15 2 15 0 16), good := (rows 23 23 23 23 16) }] }

theorem profile123_node5 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,19] 2 profile123_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,19] 2 profile123_node5_cert).mp (by decide +kernel))

def profile123_node6_cert : CutBound 5 := { lost := (rows 0 4 0 2 5), upper := (rows 23 27 23 29 26), lower := (rows 23 27 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 26 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 25 29 29 16) },{ target := 2, region := (rows 1 10 0 8 26), good := (rows 19 27 19 27 16) }] }

theorem profile123_node6 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,21] 2 profile123_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,21] 2 profile123_node6_cert).mp (by decide +kernel))

def profile123_node7_cert : CutBound 5 := { lost := (rows 8 0 8 1 6), upper := (rows 23 27 23 30 25), lower := (rows 23 27 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 26 30 30 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 25 21 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 26 16) },{ target := 3, region := (rows 15 2 15 0 16), good := (rows 23 23 23 23 16) }] }

theorem profile123_node7 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,22] 2 profile123_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19,22] 2 profile123_node7_cert).mp (by decide +kernel))

def profile123_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node4 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19] 2 (by decide) (choices 3) [19,21,22] profile123_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,19] (choices 3) [19,21,22] profile123_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile123_node5
  · exact profile123_node6
  · exact profile123_node7

def profile123_node9_cert : CutBound 5 := { lost := (rows 0 4 2 4 1), upper := (rows 23 27 29 27 22), lower := (rows 23 27 29 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 22 26 28 26 16) },{ target := 1, region := (rows 1 0 14 8 16), good := (rows 21 29 29 29 16) },{ target := 2, region := (rows 1 15 0 15 16), good := (rows 27 27 27 27 16) }] }

theorem profile123_node9 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,19] 2 profile123_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,19] 2 profile123_node9_cert).mp (by decide +kernel))

def profile123_node10_cert : CutBound 5 := { lost := (rows 0 4 2 1 4), upper := (rows 23 27 29 30 19), lower := (rows 23 27 29 30 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 26 28 30 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 28 16) },{ target := 2, region := (rows 1 6 0 8 23), good := (rows 19 27 27 26 16) }] }

theorem profile123_node10 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,22] 2 profile123_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25,22] 2 profile123_node10_cert).mp (by decide +kernel))

def profile123_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node8 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25] 2 (by decide) (choices 3) [19,22] profile123_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,25] (choices 3) [19,22] profile123_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node9
  · exact profile123_node10

def profile123_node12_cert : CutBound 5 := { lost := (rows 0 4 1 4 2), upper := (rows 23 27 30 27 21), lower := (rows 23 27 30 27 16), losses := [{ target := 0, region := (rows 0 2 14 8 16), good := (rows 22 30 30 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 21 25 28 25 16) },{ target := 2, region := (rows 1 11 0 11 16), good := (rows 27 27 26 27 16) }] }

theorem profile123_node12 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,19] 2 profile123_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,19] 2 profile123_node12_cert).mp (by decide +kernel))

def profile123_node13_cert : CutBound 5 := { lost := (rows 0 4 1 2 4), upper := (rows 23 27 30 29 19), lower := (rows 23 27 30 29 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 25 28 29 16) },{ target := 2, region := (rows 1 10 0 8 27), good := (rows 19 27 26 27 16) }] }

theorem profile123_node13 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,21] 2 profile123_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26,21] 2 profile123_node13_cert).mp (by decide +kernel))

def profile123_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node11 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26] 2 (by decide) (choices 3) [19,21] profile123_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25,26] (choices 3) [19,21] profile123_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node12
  · exact profile123_node13

def profile123_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node3 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25] 2 (by decide) (choices 3) [19,25,26] profile123_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,25] (choices 3) [19,25,26] profile123_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile123_node4
  · exact profile123_node8
  · exact profile123_node11

def profile123_node15_cert : CutBound 5 := { lost := (rows 8 0 8 4 4), upper := (rows 23 30 23 27 27), lower := (rows 23 30 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile123_node15 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,19] 2 profile123_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,19] 2 profile123_node15_cert).mp (by decide +kernel))

def profile123_node16_cert : CutBound 5 := { lost := (rows 8 1 0 4 12), upper := (rows 23 30 29 27 19), lower := (rows 23 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile123_node16 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,25] 2 profile123_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28,25] 2 profile123_node16_cert).mp (by decide +kernel))

def profile123_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node14 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28] 2 (by decide) (choices 3) [19,25] profile123_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22,28] (choices 3) [19,25] profile123_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node15
  · exact profile123_node16

def profile123_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node1 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22] 2 (by decide) (choices 3) [21,25,28] profile123_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [22] (choices 3) [21,25,28] profile123_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile123_node2
  · exact profile123_node3
  · exact profile123_node14

def profile123_node19_cert : CutBound 5 := { lost := (rows 0 8 8 4 4), upper := (rows 29 23 23 27 27), lower := (rows 29 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile123_node19 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,19] 2 profile123_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,19] 2 profile123_node19_cert).mp (by decide +kernel))

def profile123_node20_cert : CutBound 5 := { lost := (rows 2 8 0 4 12), upper := (rows 29 23 30 27 19), lower := (rows 29 23 30 8 16), losses := [{ target := 1, region := (rows 5 0 4 8 16), good := (rows 29 21 29 8 16) },{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 26 8 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile123_node20 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,26] 2 profile123_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21,26] 2 profile123_node20_cert).mp (by decide +kernel))

def profile123_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node18 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21] 2 (by decide) (choices 3) [19,26] profile123_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,21] (choices 3) [19,26] profile123_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node19
  · exact profile123_node20

def profile123_node22_cert : CutBound 5 := { lost := (rows 2 1 0 4 4), upper := (rows 29 30 23 27 19), lower := (rows 29 30 23 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 22 8 16) },{ target := 1, region := (rows 3 0 4 8 16), good := (rows 29 29 21 8 16) },{ target := 2, region := (rows 1 2 0 12 20), good := (rows 25 26 27 8 16) }] }

theorem profile123_node22 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28,19] 2 profile123_node22_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28,19] 2 profile123_node22_cert).mp (by decide +kernel))

def profile123_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile123_node21 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28] 2 (by decide) (choices 3) [19] profile123_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28,28] (choices 3) [19] profile123_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile123_node22

def profile123_node17_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile123_node17 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28] 2 (by decide) (choices 3) [21,28] profile123_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [28] (choices 3) [21,28] profile123_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node18
  · exact profile123_node21

def profile123_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile123_node0 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [] 2 (by decide) (choices 3) [22,28] profile123_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [] (choices 3) [22,28] profile123_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile123_node1
  · exact profile123_node17

theorem profile123 : Upper (D (n:=5) [51,51,50,50,36]) (R (n:=5) [51,51,50,50,36]) [] 2 := profile123_node0

#print axioms profile123
end Delivery.FiveVertexPositive14
