import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile114_node3_cert : CutBound 5 := { lost := (rows 0 8 8 4 4), upper := (rows 15 23 23 27 27), lower := (rows 15 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile114_node3 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,19] 2 profile114_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,19] 2 profile114_node3_cert).mp (by decide +kernel))

def profile114_node4_cert : CutBound 5 := { lost := (rows 0 8 0 4 12), upper := (rows 15 23 29 27 19), lower := (rows 15 23 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile114_node4 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,25] 2 profile114_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21,25] 2 profile114_node4_cert).mp (by decide +kernel))

def profile114_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node2 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21] 2 (by decide) (choices 3) [19,25] profile114_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14,21] (choices 3) [19,25] profile114_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile114_node3
  · exact profile114_node4

def profile114_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile114_node1 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14] 2 (by decide) (choices 3) [21] profile114_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [14] (choices 3) [21] profile114_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile114_node2

def profile114_node7_cert : CutBound 5 := { lost := (rows 8 0 8 4 4), upper := (rows 23 15 23 27 27), lower := (rows 23 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile114_node7 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,19] 2 profile114_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,19] 2 profile114_node7_cert).mp (by decide +kernel))

def profile114_node8_cert : CutBound 5 := { lost := (rows 8 0 0 4 12), upper := (rows 23 15 29 27 19), lower := (rows 23 15 29 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile114_node8 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,25] 2 profile114_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13,25] 2 profile114_node8_cert).mp (by decide +kernel))

def profile114_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node6 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13] 2 (by decide) (choices 3) [19,25] profile114_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,13] (choices 3) [19,25] profile114_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile114_node7
  · exact profile114_node8

def profile114_node9_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile114_node9 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,21] 2 profile114_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,21] 2 profile114_node9_cert).mp (by decide +kernel))

def profile114_node12_cert : CutBound 5 := { lost := (rows 8 4 0 4 10), upper := (rows 23 27 15 27 21), lower := (rows 23 27 15 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 25 29 25 16) },{ target := 2, region := (rows 1 11 0 11 16), good := (rows 27 27 11 27 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 19 16) }] }

theorem profile114_node12 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,19] 2 profile114_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,19] 2 profile114_node12_cert).mp (by decide +kernel))

def profile114_node13_cert : CutBound 5 := { lost := (rows 8 4 0 2 12), upper := (rows 23 27 15 29 19), lower := (rows 23 27 15 29 16), losses := [{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 25 13 29 16) },{ target := 2, region := (rows 1 14 0 8 31), good := (rows 19 27 27 27 16) },{ target := 3, region := (rows 5 2 4 0 23), good := (rows 23 19 23 21 16) }] }

theorem profile114_node13 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,21] 2 profile114_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11,21] 2 profile114_node13_cert).mp (by decide +kernel))

def profile114_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node11 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11] 2 (by decide) (choices 3) [19,21] profile114_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,11] (choices 3) [19,21] profile114_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile114_node12
  · exact profile114_node13

def profile114_node15_cert : CutBound 5 := { lost := (rows 8 4 8 0 6), upper := (rows 23 27 23 15 25), lower := (rows 23 27 23 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 26), good := (rows 21 25 21 29 16) },{ target := 2, region := (rows 1 10 0 8 26), good := (rows 19 27 19 27 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile114_node15 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19,7] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19,7] 2 profile114_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19,7] 2 profile114_node15_cert).mp (by decide +kernel))

def profile114_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node14 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19] 2 (by decide) (choices 3) [7] profile114_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,19] (choices 3) [7] profile114_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile114_node15

def profile114_node16_cert : CutBound 5 := { lost := (rows 0 4 2 16 8), upper := (rows 23 27 29 15 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile114_node16 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,25] 2 profile114_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25,25] 2 profile114_node16_cert).mp (by decide +kernel))

def profile114_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node10 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25] 2 (by decide) (choices 3) [11,19,25] profile114_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22,25] (choices 3) [11,19,25] profile114_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile114_node11
  · exact profile114_node14
  · exact profile114_node16

def profile114_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node5 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22] 2 (by decide) (choices 3) [13,21,25] profile114_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [22] (choices 3) [13,21,25] profile114_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile114_node6
  · exact profile114_node9
  · exact profile114_node10

def profile114_node18_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 29 15 23 27 19), lower := (rows 29 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) },{ target := 3, region := (rows 1 2 6 0 18), good := (rows 21 23 4 0 16) }] }

theorem profile114_node18 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,13] 2 profile114_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,13] 2 profile114_node18_cert).mp (by decide +kernel))

def profile114_node20_cert : CutBound 5 := { lost := (rows 0 8 0 4 12), upper := (rows 29 23 15 27 19), lower := (rows 29 23 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile114_node20 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,11] 2 profile114_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,11] 2 profile114_node20_cert).mp (by decide +kernel))

def profile114_node21_cert : CutBound 5 := { lost := (rows 0 8 8 4 4), upper := (rows 29 23 23 11 27), lower := (rows 29 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 14 22), good := (rows 25 27 27 8 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile114_node21 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,19] 2 profile114_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21,19] 2 profile114_node21_cert).mp (by decide +kernel))

def profile114_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile114_node19 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21] 2 (by decide) (choices 3) [11,19] profile114_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28,21] (choices 3) [11,19] profile114_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile114_node20
  · exact profile114_node21

def profile114_node17_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile114_node17 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28] 2 (by decide) (choices 3) [13,21] profile114_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [28] (choices 3) [13,21] profile114_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile114_node18
  · exact profile114_node19

def profile114_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile114_node0 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [] 2 (by decide) (choices 3) [14,22,28] profile114_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [] (choices 3) [14,22,28] profile114_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile114_node1
  · exact profile114_node5
  · exact profile114_node17

theorem profile114 : Upper (D (n:=5) [52,51,50,50,35]) (R (n:=5) [52,51,50,50,35]) [] 2 := profile114_node0

def profile115_node4_cert : CutBound 5 := { lost := (rows 0 8 8 4 3), upper := (rows 15 23 23 27 28), lower := (rows 15 23 23 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 26 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 25 16) },{ target := 2, region := (rows 1 2 0 14 16), good := (rows 11 27 27 27 16) },{ target := 3, region := (rows 1 14 14 0 16), good := (rows 7 23 23 23 16) }] }

theorem profile115_node4 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,19] 2 profile115_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,19] 2 profile115_node4_cert).mp (by decide +kernel))

def profile115_node5_cert : CutBound 5 := { lost := (rows 0 8 8 2 5), upper := (rows 15 23 23 29 26), lower := (rows 15 23 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 17), good := (rows 30 22 22 28 16) },{ target := 1, region := (rows 1 0 4 14 16), good := (rows 13 29 29 29 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 25 16) },{ target := 3, region := (rows 1 14 14 0 16), good := (rows 7 23 23 23 16) }] }

theorem profile115_node5 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,21] 2 profile115_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,21] 2 profile115_node5_cert).mp (by decide +kernel))

def profile115_node6_cert : CutBound 5 := { lost := (rows 0 8 8 1 6), upper := (rows 15 23 23 30 25), lower := (rows 15 23 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 14 30 30 30 16) },{ target := 1, region := (rows 1 0 4 8 17), good := (rows 29 21 21 28 16) },{ target := 2, region := (rows 1 2 0 8 17), good := (rows 27 19 19 26 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 22 16) }] }

theorem profile115_node6 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,22] 2 profile115_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19,22] 2 profile115_node6_cert).mp (by decide +kernel))

def profile115_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node3 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19] 2 (by decide) (choices 3) [19,21,22] profile115_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,19] (choices 3) [19,21,22] profile115_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node4
  · exact profile115_node5
  · exact profile115_node6

def profile115_node8_cert : CutBound 5 := { lost := (rows 0 8 2 4 9), upper := (rows 15 23 29 27 22), lower := (rows 15 23 29 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 22 28 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 13 21 29 29 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 25 27 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 19 16) }] }

theorem profile115_node8 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,19] 2 profile115_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,19] 2 profile115_node8_cert).mp (by decide +kernel))

def profile115_node9_cert : CutBound 5 := { lost := (rows 0 8 0 1 12), upper := (rows 15 23 29 30 19), lower := (rows 15 23 29 30 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 28 30 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 25 26 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile115_node9 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,22] 2 profile115_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25,22] 2 profile115_node9_cert).mp (by decide +kernel))

def profile115_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node7 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25] 2 (by decide) (choices 3) [19,22] profile115_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,25] (choices 3) [19,22] profile115_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node8
  · exact profile115_node9

def profile115_node11_cert : CutBound 5 := { lost := (rows 0 8 1 4 10), upper := (rows 15 23 30 27 21), lower := (rows 15 23 30 27 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 14 22 30 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 21 28 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 26 27 16) },{ target := 3, region := (rows 1 3 4 0 19), good := (rows 23 23 22 19 16) }] }

theorem profile115_node11 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,19] 2 profile115_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,19] 2 profile115_node11_cert).mp (by decide +kernel))

def profile115_node12_cert : CutBound 5 := { lost := (rows 0 8 0 2 12), upper := (rows 15 23 30 29 19), lower := (rows 15 23 30 29 16), losses := [{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 28 29 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 19 26 25 16) },{ target := 3, region := (rows 1 11 4 0 27), good := (rows 23 23 22 23 16) }] }

theorem profile115_node12 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,21] 2 profile115_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26,21] 2 profile115_node12_cert).mp (by decide +kernel))

def profile115_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node10 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26] 2 (by decide) (choices 3) [19,21] profile115_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21,26] (choices 3) [19,21] profile115_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node11
  · exact profile115_node12

def profile115_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node2 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21] 2 (by decide) (choices 3) [19,25,26] profile115_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,21] (choices 3) [19,25,26] profile115_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node3
  · exact profile115_node7
  · exact profile115_node10

def profile115_node15_cert : CutBound 5 := { lost := (rows 0 4 8 2 9), upper := (rows 15 27 23 29 22), lower := (rows 15 27 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 22 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 25 29 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 11 27 19 27 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile115_node15 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,21] 2 profile115_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,21] 2 profile115_node15_cert).mp (by decide +kernel))

def profile115_node16_cert : CutBound 5 := { lost := (rows 0 0 8 1 10), upper := (rows 15 27 23 30 21), lower := (rows 15 27 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 26 30 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 21 28 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile115_node16 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,22] 2 profile115_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19,22] 2 profile115_node16_cert).mp (by decide +kernel))

def profile115_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node14 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19] 2 (by decide) (choices 3) [21,22] profile115_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25,19] (choices 3) [21,22] profile115_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node15
  · exact profile115_node16

def profile115_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node13 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25] 2 (by decide) (choices 3) [19] profile115_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,25] (choices 3) [19] profile115_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node14

def profile115_node19_cert : CutBound 5 := { lost := (rows 0 0 8 4 10), upper := (rows 15 30 23 27 21), lower := (rows 15 30 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 21 25 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 26 27 27 16) },{ target := 3, region := (rows 1 2 13 0 29), good := (rows 23 22 23 23 16) }] }

theorem profile115_node19 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,19] 2 profile115_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,19] 2 profile115_node19_cert).mp (by decide +kernel))

def profile115_node20_cert : CutBound 5 := { lost := (rows 0 1 8 2 12), upper := (rows 15 30 23 29 19), lower := (rows 15 30 23 29 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 14 30 22 30 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 28 29 29 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 19 25 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 21 16) }] }

theorem profile115_node20 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,21] 2 profile115_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19,21] 2 profile115_node20_cert).mp (by decide +kernel))

def profile115_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node18 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19] 2 (by decide) (choices 3) [19,21] profile115_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28,19] (choices 3) [19,21] profile115_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node19
  · exact profile115_node20

def profile115_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node17 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28] 2 (by decide) (choices 3) [19] profile115_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14,28] (choices 3) [19] profile115_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node18

def profile115_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node1 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14] 2 (by decide) (choices 3) [21,25,28] profile115_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [14] (choices 3) [21,25,28] profile115_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node2
  · exact profile115_node13
  · exact profile115_node17

def profile115_node24_cert : CutBound 5 := { lost := (rows 8 0 8 4 3), upper := (rows 23 15 23 27 28), lower := (rows 23 15 23 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 29 21 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 11 27 27 16) },{ target := 3, region := (rows 13 2 13 0 16), good := (rows 23 7 23 23 16) }] }

theorem profile115_node24 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,19] 2 profile115_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,19] 2 profile115_node24_cert).mp (by decide +kernel))

def profile115_node25_cert : CutBound 5 := { lost := (rows 8 0 8 2 5), upper := (rows 23 15 23 29 26), lower := (rows 23 15 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 18), good := (rows 22 30 22 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 13 29 29 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 25 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 21 16) }] }

theorem profile115_node25 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,21] 2 profile115_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,21] 2 profile115_node25_cert).mp (by decide +kernel))

def profile115_node26_cert : CutBound 5 := { lost := (rows 8 0 8 1 6), upper := (rows 23 15 23 30 25), lower := (rows 23 15 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 18), good := (rows 21 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 19 26 16) },{ target := 3, region := (rows 13 2 13 0 16), good := (rows 23 7 23 23 16) }] }

theorem profile115_node26 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,22] 2 profile115_node26_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19,22] 2 profile115_node26_cert).mp (by decide +kernel))

def profile115_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node23 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19] 2 (by decide) (choices 3) [19,21,22] profile115_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,19] (choices 3) [19,21,22] profile115_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node24
  · exact profile115_node25
  · exact profile115_node26

def profile115_node28_cert : CutBound 5 := { lost := (rows 8 0 2 4 9), upper := (rows 23 15 29 27 22), lower := (rows 23 15 29 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 22 30 28 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 21 13 29 29 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 25 27 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 19 16) }] }

theorem profile115_node28 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,19] 2 profile115_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,19] 2 profile115_node28_cert).mp (by decide +kernel))

def profile115_node29_cert : CutBound 5 := { lost := (rows 8 0 0 1 12), upper := (rows 23 15 29 30 19), lower := (rows 23 15 29 30 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 28 30 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 19 27 25 26 16) },{ target := 3, region := (rows 11 2 4 0 27), good := (rows 23 23 21 23 16) }] }

theorem profile115_node29 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,22] 2 profile115_node29_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25,22] 2 profile115_node29_cert).mp (by decide +kernel))

def profile115_node27_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node27 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25] 2 (by decide) (choices 3) [19,22] profile115_node27_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,25] (choices 3) [19,22] profile115_node27_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node28
  · exact profile115_node29

def profile115_node31_cert : CutBound 5 := { lost := (rows 8 0 1 4 10), upper := (rows 23 15 30 27 21), lower := (rows 23 15 30 27 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 22 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 21 29 28 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 26 27 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 19 16) }] }

theorem profile115_node31 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,19] 2 profile115_node31_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,19] 2 profile115_node31_cert).mp (by decide +kernel))

def profile115_node32_cert : CutBound 5 := { lost := (rows 8 0 0 2 12), upper := (rows 23 15 30 29 19), lower := (rows 23 15 30 29 16), losses := [{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 28 29 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 19 27 26 25 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile115_node32 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,21] 2 profile115_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26,21] 2 profile115_node32_cert).mp (by decide +kernel))

def profile115_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node30 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26] 2 (by decide) (choices 3) [19,21] profile115_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13,26] (choices 3) [19,21] profile115_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node31
  · exact profile115_node32

def profile115_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node22 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13] 2 (by decide) (choices 3) [19,25,26] profile115_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,13] (choices 3) [19,25,26] profile115_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node23
  · exact profile115_node27
  · exact profile115_node30

def profile115_node35_cert : CutBound 5 := { lost := (rows 8 8 0 4 3), upper := (rows 23 23 15 27 28), lower := (rows 23 23 15 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 22 30 26 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 21 29 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 27 11 27 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 7 19 16) }] }

theorem profile115_node35 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,19] 2 profile115_node35_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,19] 2 profile115_node35_cert).mp (by decide +kernel))

def profile115_node36_cert : CutBound 5 := { lost := (rows 8 8 0 2 5), upper := (rows 23 23 15 29 26), lower := (rows 23 23 15 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 20), good := (rows 22 22 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 29 13 29 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 19 19 27 25 16) },{ target := 3, region := (rows 11 11 4 0 16), good := (rows 23 23 7 23 16) }] }

theorem profile115_node36 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,21] 2 profile115_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,21] 2 profile115_node36_cert).mp (by decide +kernel))

def profile115_node37_cert : CutBound 5 := { lost := (rows 8 8 0 1 6), upper := (rows 23 23 15 30 25), lower := (rows 23 23 15 30 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 30 14 30 16) },{ target := 1, region := (rows 1 0 4 8 20), good := (rows 21 21 29 28 16) },{ target := 2, region := (rows 1 2 0 8 20), good := (rows 19 19 27 26 16) },{ target := 3, region := (rows 11 11 4 0 16), good := (rows 23 23 7 23 16) }] }

theorem profile115_node37 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,22] 2 profile115_node37_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11,22] 2 profile115_node37_cert).mp (by decide +kernel))

def profile115_node34_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node34 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11] 2 (by decide) (choices 3) [19,21,22] profile115_node34_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,11] (choices 3) [19,21,22] profile115_node34_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node35
  · exact profile115_node36
  · exact profile115_node37

def profile115_node39_cert : CutBound 5 := { lost := (rows 8 8 0 0 5), upper := (rows 23 23 29 15 26), lower := (rows 23 23 29 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 24), good := (rows 22 22 28 30 16) },{ target := 2, region := (rows 1 2 0 8 24), good := (rows 19 19 25 27 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile115_node39 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25,7] 2 profile115_node39_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25,7] 2 profile115_node39_cert).mp (by decide +kernel))

def profile115_node38_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node38 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25] 2 (by decide) (choices 3) [7] profile115_node38_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,25] (choices 3) [7] profile115_node38_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node39

def profile115_node41_cert : CutBound 5 := { lost := (rows 8 8 0 0 6), upper := (rows 23 23 30 15 25), lower := (rows 23 23 30 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 24), good := (rows 21 21 28 29 16) },{ target := 2, region := (rows 1 2 0 8 24), good := (rows 19 19 26 27 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile115_node41 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26,7] 2 profile115_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26,7] 2 profile115_node41_cert).mp (by decide +kernel))

def profile115_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node40 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26] 2 (by decide) (choices 3) [7] profile115_node40_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21,26] (choices 3) [7] profile115_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node41

def profile115_node33_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node33 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21] 2 (by decide) (choices 3) [11,25,26] profile115_node33_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,21] (choices 3) [11,25,26] profile115_node33_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node34
  · exact profile115_node38
  · exact profile115_node40

def profile115_node44_cert : CutBound 5 := { lost := (rows 8 4 0 2 9), upper := (rows 23 27 15 29 22), lower := (rows 23 27 15 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 22 26 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 25 13 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 19 27 11 27 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 21 16) }] }

theorem profile115_node44 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,21] 2 profile115_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,21] 2 profile115_node44_cert).mp (by decide +kernel))

def profile115_node45_cert : CutBound 5 := { lost := (rows 8 0 0 1 10), upper := (rows 23 27 15 30 21), lower := (rows 23 27 15 30 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 26 14 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 25 29 28 16) },{ target := 3, region := (rows 13 2 4 0 29), good := (rows 23 19 23 23 16) }] }

theorem profile115_node45 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,22] 2 profile115_node45_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11,22] 2 profile115_node45_cert).mp (by decide +kernel))

def profile115_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node43 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11] 2 (by decide) (choices 3) [21,22] profile115_node43_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,11] (choices 3) [21,22] profile115_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node44
  · exact profile115_node45

def profile115_node47_cert : CutBound 5 := { lost := (rows 8 0 8 0 3), upper := (rows 23 27 23 15 28), lower := (rows 23 27 23 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 24), good := (rows 22 26 22 30 16) },{ target := 1, region := (rows 1 0 4 8 24), good := (rows 21 25 21 29 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile115_node47 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19,7] 2 profile115_node47_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19,7] 2 profile115_node47_cert).mp (by decide +kernel))

def profile115_node46_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node46 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19] 2 (by decide) (choices 3) [7] profile115_node46_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,19] (choices 3) [7] profile115_node46_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node47

def profile115_node48_cert : CutBound 5 := { lost := (rows 0 4 2 16 8), upper := (rows 23 27 29 15 23), lower := (rows 23 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 6 8 16), good := (rows 21 29 29 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 19 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile115_node48 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,25] 2 profile115_node48_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,25] 2 profile115_node48_cert).mp (by decide +kernel))

def profile115_node49_cert : CutBound 5 := { lost := (rows 8 0 1 16 8), upper := (rows 23 27 30 15 23), lower := (rows 23 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 30 30 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 14 8 0) }] }

theorem profile115_node49 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,26] 2 profile115_node49_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25,26] 2 profile115_node49_cert).mp (by decide +kernel))

def profile115_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node42 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25] 2 (by decide) (choices 3) [11,19,25,26] profile115_node42_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,25] (choices 3) [11,19,25,26] profile115_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile115_node43
  · exact profile115_node46
  · exact profile115_node48
  · exact profile115_node49

def profile115_node52_cert : CutBound 5 := { lost := (rows 8 0 0 4 10), upper := (rows 23 30 15 27 21), lower := (rows 23 30 15 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 28 29 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 26 11 27 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 19 16) }] }

theorem profile115_node52 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,19] 2 profile115_node52_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,19] 2 profile115_node52_cert).mp (by decide +kernel))

def profile115_node53_cert : CutBound 5 := { lost := (rows 8 1 0 2 12), upper := (rows 23 30 15 29 19), lower := (rows 23 30 15 29 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 22 30 14 30 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 28 13 29 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 19 26 27 25 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile115_node53 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,21] 2 profile115_node53_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11,21] 2 profile115_node53_cert).mp (by decide +kernel))

def profile115_node51_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node51 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11] 2 (by decide) (choices 3) [19,21] profile115_node51_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,11] (choices 3) [19,21] profile115_node51_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node52
  · exact profile115_node53

def profile115_node55_cert : CutBound 5 := { lost := (rows 8 0 8 0 6), upper := (rows 23 30 23 15 25), lower := (rows 23 30 23 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 24), good := (rows 21 28 21 29 16) },{ target := 2, region := (rows 1 2 0 8 24), good := (rows 19 26 19 27 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile115_node55 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19,7] 2 profile115_node55_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19,7] 2 profile115_node55_cert).mp (by decide +kernel))

def profile115_node54_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node54 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19] 2 (by decide) (choices 3) [7] profile115_node54_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,19] (choices 3) [7] profile115_node54_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node55

def profile115_node56_cert : CutBound 5 := { lost := (rows 8 1 0 16 8), upper := (rows 23 30 29 15 23), lower := (rows 23 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 22 30 30 8 16) },{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 14 13 8 0) }] }

theorem profile115_node56 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,25] 2 profile115_node56_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28,25] 2 profile115_node56_cert).mp (by decide +kernel))

def profile115_node50_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node50 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28] 2 (by decide) (choices 3) [11,19,25] profile115_node50_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22,28] (choices 3) [11,19,25] profile115_node50_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node51
  · exact profile115_node54
  · exact profile115_node56

def profile115_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node21 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22] 2 (by decide) (choices 3) [13,21,25,28] profile115_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [22] (choices 3) [13,21,25,28] profile115_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile115_node22
  · exact profile115_node33
  · exact profile115_node42
  · exact profile115_node50

def profile115_node60_cert : CutBound 5 := { lost := (rows 0 0 8 2 9), upper := (rows 27 15 23 29 22), lower := (rows 27 15 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 30 22 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 25 13 29 29 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 21 16) }] }

theorem profile115_node60 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,21] 2 profile115_node60_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,21] 2 profile115_node60_cert).mp (by decide +kernel))

def profile115_node61_cert : CutBound 5 := { lost := (rows 4 0 8 1 10), upper := (rows 27 15 23 30 21), lower := (rows 27 15 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 26 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 29 21 28 16) },{ target := 2, region := (rows 9 2 0 8 16), good := (rows 27 11 19 27 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 22 16) }] }

theorem profile115_node61 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,22] 2 profile115_node61_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19,22] 2 profile115_node61_cert).mp (by decide +kernel))

def profile115_node59_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node59 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19] 2 (by decide) (choices 3) [21,22] profile115_node59_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13,19] (choices 3) [21,22] profile115_node59_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node60
  · exact profile115_node61

def profile115_node58_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node58 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13] 2 (by decide) (choices 3) [19] profile115_node58_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,13] (choices 3) [19] profile115_node58_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node59

def profile115_node64_cert : CutBound 5 := { lost := (rows 0 8 0 2 9), upper := (rows 27 23 15 29 22), lower := (rows 27 23 15 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 22 30 28 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 25 29 13 29 16) },{ target := 3, region := (rows 1 14 4 0 30), good := (rows 19 23 23 23 16) }] }

theorem profile115_node64 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,21] 2 profile115_node64_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,21] 2 profile115_node64_cert).mp (by decide +kernel))

def profile115_node65_cert : CutBound 5 := { lost := (rows 4 8 0 1 10), upper := (rows 27 23 15 30 21), lower := (rows 27 23 15 30 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 26 30 14 30 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 21 29 28 16) },{ target := 2, region := (rows 9 2 0 8 16), good := (rows 27 19 11 27 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 22 16) }] }

theorem profile115_node65 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,22] 2 profile115_node65_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11,22] 2 profile115_node65_cert).mp (by decide +kernel))

def profile115_node63_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node63 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11] 2 (by decide) (choices 3) [21,22] profile115_node63_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,11] (choices 3) [21,22] profile115_node63_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile115_node64
  · exact profile115_node65

def profile115_node67_cert : CutBound 5 := { lost := (rows 0 8 8 0 3), upper := (rows 27 23 23 15 28), lower := (rows 27 23 23 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 24), good := (rows 26 22 22 30 16) },{ target := 1, region := (rows 1 0 4 8 24), good := (rows 25 21 21 29 16) },{ target := 3, region := (rows 1 7 7 0 16), good := (rows 23 23 23 7 16) }] }

theorem profile115_node67 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19,7] 2 profile115_node67_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19,7] 2 profile115_node67_cert).mp (by decide +kernel))

def profile115_node66_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node66 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19] 2 (by decide) (choices 3) [7] profile115_node66_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,19] (choices 3) [7] profile115_node66_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node67

def profile115_node68_cert : CutBound 5 := { lost := (rows 0 8 2 16 8), upper := (rows 27 23 29 15 23), lower := (rows 27 23 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 21 29 8 16) },{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 13 8 0) }] }

theorem profile115_node68 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,25] 2 profile115_node68_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,25] 2 profile115_node68_cert).mp (by decide +kernel))

def profile115_node69_cert : CutBound 5 := { lost := (rows 4 0 1 16 8), upper := (rows 27 23 30 15 23), lower := (rows 27 23 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 22 30 8 16) },{ target := 2, region := (rows 5 2 0 8 16), good := (rows 27 19 27 8 16) },{ target := 3, region := (rows 1 2 4 0 18), good := (rows 19 23 22 0 16) },{ target := 4, region := (rows 1 2 4 10 0), good := (rows 11 15 14 8 0) }] }

theorem profile115_node69 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,26] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,26] 2 profile115_node69_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21,26] 2 profile115_node69_cert).mp (by decide +kernel))

def profile115_node62_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node62 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21] 2 (by decide) (choices 3) [11,19,25,26] profile115_node62_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,21] (choices 3) [11,19,25,26] profile115_node62_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile115_node63
  · exact profile115_node66
  · exact profile115_node68
  · exact profile115_node69

def profile115_node71_cert : CutBound 5 := { lost := (rows 4 0 8 16 8), upper := (rows 27 30 23 15 23), lower := (rows 27 30 23 8 16), losses := [{ target := 2, region := (rows 3 2 0 8 16), good := (rows 27 27 19 8 16) },{ target := 3, region := (rows 1 2 5 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 4 12 0), good := (rows 11 14 15 8 0) }] }

theorem profile115_node71 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28,19] 2 profile115_node71_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28,19] 2 profile115_node71_cert).mp (by decide +kernel))

def profile115_node70_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node70 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28] 2 (by decide) (choices 3) [19] profile115_node70_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26,28] (choices 3) [19] profile115_node70_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile115_node71

def profile115_node57_route : Route 5 := (fun mask => (mask,id))

theorem profile115_node57 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26] 2 (by decide) (choices 3) [13,21,28] profile115_node57_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [26] (choices 3) [13,21,28] profile115_node57_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node58
  · exact profile115_node62
  · exact profile115_node70

def profile115_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile115_node0 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [] 2 (by decide) (choices 3) [14,22,26] profile115_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [] (choices 3) [14,22,26] profile115_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile115_node1
  · exact profile115_node21
  · exact profile115_node57

theorem profile115 : Upper (D (n:=5) [51,51,51,50,35]) (R (n:=5) [51,51,51,50,35]) [] 2 := profile115_node0

def profile116_node3_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 27 29 27 27), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile116_node3 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,25] 2 profile116_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,25] 2 profile116_node3_cert).mp (by decide +kernel))

def profile116_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 27 30 25 25), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile116_node4 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,26] 2 profile116_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25,26] 2 profile116_node4_cert).mp (by decide +kernel))

def profile116_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile116_node2 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25] 2 (by decide) (choices 3) [25,26] profile116_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30,25] (choices 3) [25,26] profile116_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile116_node3
  · exact profile116_node4

def profile116_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile116_node1 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30] 2 (by decide) (choices 3) [25] profile116_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [30] (choices 3) [25] profile116_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile116_node2

def profile116_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile116_node0 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [] 2 (by decide) (choices 4) [30] profile116_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [] (choices 4) [30] profile116_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile116_node1

theorem profile116 : Upper (D (n:=5) [67,50,49,36,36]) (R (n:=5) [67,50,49,36,36]) [] 2 := profile116_node0

def profile117_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 27 29 26 26), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 26 28 8 16) }] }

theorem profile117_node3 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,25] 2 profile117_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,25] 2 profile117_node3_cert).mp (by decide +kernel))

def profile117_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 27 30 27 27), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile117_node4 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,26] 2 profile117_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25,26] 2 profile117_node4_cert).mp (by decide +kernel))

def profile117_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile117_node2 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25] 2 (by decide) (choices 3) [25,26] profile117_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30,25] (choices 3) [25,26] profile117_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile117_node3
  · exact profile117_node4

def profile117_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile117_node1 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30] 2 (by decide) (choices 3) [25] profile117_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [30] (choices 3) [25] profile117_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile117_node2

def profile117_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile117_node0 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [] 2 (by decide) (choices 4) [30] profile117_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [] (choices 4) [30] profile117_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile117_node1

theorem profile117 : Upper (D (n:=5) [66,51,49,36,36]) (R (n:=5) [66,51,49,36,36]) [] 2 := profile117_node0

def profile118_node3_cert : CutBound 5 := { lost := (rows 0 4 2 1 1), upper := (rows 31 27 29 30 30), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile118_node3 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,25] 2 profile118_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,25] 2 profile118_node3_cert).mp (by decide +kernel))

def profile118_node4_cert : CutBound 5 := { lost := (rows 0 4 1 2 2), upper := (rows 31 27 30 29 29), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) }] }

theorem profile118_node4 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,26] 2 profile118_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25,26] 2 profile118_node4_cert).mp (by decide +kernel))

def profile118_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile118_node2 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25] 2 (by decide) (choices 3) [25,26] profile118_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,25] (choices 3) [25,26] profile118_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile118_node3
  · exact profile118_node4

def profile118_node6_cert : CutBound 5 := { lost := (rows 0 1 2 4 4), upper := (rows 31 30 29 27 27), lower := (rows 31 30 29 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) }] }

theorem profile118_node6 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,25] 2 profile118_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,25] 2 profile118_node6_cert).mp (by decide +kernel))

def profile118_node7_cert : CutBound 5 := { lost := (rows 0 1 1 2 2), upper := (rows 31 30 30 25 25), lower := (rows 31 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 28 28 8 16) }] }

theorem profile118_node7 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,26] 2 profile118_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28,26] 2 profile118_node7_cert).mp (by decide +kernel))

def profile118_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile118_node5 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28] 2 (by decide) (choices 3) [25,26] profile118_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30,28] (choices 3) [25,26] profile118_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile118_node6
  · exact profile118_node7

def profile118_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile118_node1 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30] 2 (by decide) (choices 3) [25,28] profile118_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [30] (choices 3) [25,28] profile118_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile118_node2
  · exact profile118_node5

def profile118_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile118_node0 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [] 2 := by
  apply routed_branch (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [] 2 (by decide) (choices 4) [30] profile118_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [] (choices 4) [30] profile118_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile118_node1

theorem profile118 : Upper (D (n:=5) [66,50,50,36,36]) (R (n:=5) [66,50,50,36,36]) [] 2 := profile118_node0

def profile119_node2_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 30 30 30), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile119_node2 : Upper (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,25] 2 profile119_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,25] 2 profile119_node2_cert).mp (by decide +kernel))

def profile119_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile119_node3 : Upper (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,28] 2 profile119_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30,28] 2 profile119_node3_cert).mp (by decide +kernel))

def profile119_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile119_node1 : Upper (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30] 2 (by decide) (choices 3) [25,28] profile119_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [30] (choices 3) [25,28] profile119_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile119_node2
  · exact profile119_node3

def profile119_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile119_node0 : Upper (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [] 2 (by decide) (choices 4) [30] profile119_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [] (choices 4) [30] profile119_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile119_node1

theorem profile119 : Upper (D (n:=5) [65,51,50,36,36]) (R (n:=5) [65,51,50,36,36]) [] 2 := profile119_node0

def profile120_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile120_node2 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,21] 2 profile120_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,21] 2 profile120_node2_cert).mp (by decide +kernel))

def profile120_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 23 27 23 27 21), lower := (rows 23 27 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 25 21 25 16) }] }

theorem profile120_node5 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,19] 2 profile120_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,19] 2 profile120_node5_cert).mp (by decide +kernel))

def profile120_node6_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 27 23 29 19), lower := (rows 23 27 23 29 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 25 29 29 16) }] }

theorem profile120_node6 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,21] 2 profile120_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19,21] 2 profile120_node6_cert).mp (by decide +kernel))

def profile120_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node4 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19] 2 (by decide) (choices 3) [19,21] profile120_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25,19] (choices 3) [19,21] profile120_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile120_node5
  · exact profile120_node6

def profile120_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node3 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25] 2 (by decide) (choices 3) [19] profile120_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22,25] (choices 3) [19] profile120_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile120_node4

def profile120_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node1 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22] 2 (by decide) (choices 3) [21,25] profile120_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [22] (choices 3) [21,25] profile120_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile120_node2
  · exact profile120_node3

def profile120_node10_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 27 23 23 27 21), lower := (rows 27 23 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 22), good := (rows 25 21 21 25 16) }] }

theorem profile120_node10 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,19] 2 profile120_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,19] 2 profile120_node10_cert).mp (by decide +kernel))

def profile120_node11_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 27 23 23 29 19), lower := (rows 27 23 23 29 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 25 29 29 29 16) }] }

theorem profile120_node11 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,21] 2 profile120_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19,21] 2 profile120_node11_cert).mp (by decide +kernel))

def profile120_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node9 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19] 2 (by decide) (choices 3) [19,21] profile120_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21,19] (choices 3) [19,21] profile120_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile120_node10
  · exact profile120_node11

def profile120_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node8 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21] 2 (by decide) (choices 3) [19] profile120_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26,21] (choices 3) [19] profile120_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile120_node9

def profile120_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node7 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26] 2 (by decide) (choices 3) [21] profile120_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [26] (choices 3) [21] profile120_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile120_node8

def profile120_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 29 23 23 27 19), lower := (rows 29 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 10 18), good := (rows 25 27 0 8 16) }] }

theorem profile120_node13 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28,21] 2 profile120_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28,21] 2 profile120_node13_cert).mp (by decide +kernel))

def profile120_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node12 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28] 2 (by decide) (choices 3) [21] profile120_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [28] (choices 3) [21] profile120_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile120_node13

def profile120_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile120_node0 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [] 2 (by decide) (choices 3) [22,26,28] profile120_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [] (choices 3) [22,26,28] profile120_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile120_node1
  · exact profile120_node7
  · exact profile120_node12

theorem profile120 : Upper (D (n:=5) [52,51,50,49,36]) (R (n:=5) [52,51,50,49,36]) [] 2 := profile120_node0

def profile121_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 23 23 27 28), lower := (rows 23 23 23 27 16), losses := [{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 27 27 27 16) }] }

theorem profile121_node4 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,19] 2 profile121_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,19] 2 profile121_node4_cert).mp (by decide +kernel))

def profile121_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 23 23 29 26), lower := (rows 23 23 23 29 16), losses := [{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 29 29 29 16) }] }

theorem profile121_node5 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,21] 2 profile121_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,21] 2 profile121_node5_cert).mp (by decide +kernel))

def profile121_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 23 23 30 25), lower := (rows 23 23 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 30 30 30 16) }] }

theorem profile121_node6 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,22] 2 profile121_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19,22] 2 profile121_node6_cert).mp (by decide +kernel))

def profile121_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node3 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19] 2 (by decide) (choices 3) [19,21,22] profile121_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,19] (choices 3) [19,21,22] profile121_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile121_node4
  · exact profile121_node5
  · exact profile121_node6

def profile121_node8_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 23 23 29 27 22), lower := (rows 23 23 29 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 22 22 28 26 16) }] }

theorem profile121_node8 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,19] 2 profile121_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,19] 2 profile121_node8_cert).mp (by decide +kernel))

def profile121_node9_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 23 29 30 19), lower := (rows 23 23 29 30 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 30 28 30 16) }] }

theorem profile121_node9 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,22] 2 profile121_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25,22] 2 profile121_node9_cert).mp (by decide +kernel))

def profile121_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node7 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25] 2 (by decide) (choices 3) [19,22] profile121_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,25] (choices 3) [19,22] profile121_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node8
  · exact profile121_node9

def profile121_node11_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 23 30 27 21), lower := (rows 23 23 30 27 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 22 22 30 30 16) }] }

theorem profile121_node11 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,19] 2 profile121_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,19] 2 profile121_node11_cert).mp (by decide +kernel))

def profile121_node12_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 23 30 29 19), lower := (rows 23 23 30 29 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 29 28 29 16) }] }

theorem profile121_node12 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,21] 2 profile121_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26,21] 2 profile121_node12_cert).mp (by decide +kernel))

def profile121_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node10 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26] 2 (by decide) (choices 3) [19,21] profile121_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21,26] (choices 3) [19,21] profile121_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node11
  · exact profile121_node12

def profile121_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node2 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21] 2 (by decide) (choices 3) [19,25,26] profile121_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,21] (choices 3) [19,25,26] profile121_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile121_node3
  · exact profile121_node7
  · exact profile121_node10

def profile121_node15_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 23 27 23 29 22), lower := (rows 23 27 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 22 26 22 28 16) }] }

theorem profile121_node15 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,21] 2 profile121_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,21] 2 profile121_node15_cert).mp (by decide +kernel))

def profile121_node16_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 27 23 30 21), lower := (rows 23 27 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 26 30 30 16) }] }

theorem profile121_node16 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,22] 2 profile121_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19,22] 2 profile121_node16_cert).mp (by decide +kernel))

def profile121_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node14 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19] 2 (by decide) (choices 3) [21,22] profile121_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25,19] (choices 3) [21,22] profile121_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node15
  · exact profile121_node16

def profile121_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node13 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25] 2 (by decide) (choices 3) [19] profile121_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,25] (choices 3) [19] profile121_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile121_node14

def profile121_node19_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 23 30 23 27 21), lower := (rows 23 30 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 28 21 25 16) }] }

theorem profile121_node19 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,19] 2 profile121_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,19] 2 profile121_node19_cert).mp (by decide +kernel))

def profile121_node20_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 23 30 23 29 19), lower := (rows 23 30 23 29 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 22 30 22 30 16) }] }

theorem profile121_node20 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,21] 2 profile121_node20_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19,21] 2 profile121_node20_cert).mp (by decide +kernel))

def profile121_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node18 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19] 2 (by decide) (choices 3) [19,21] profile121_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28,19] (choices 3) [19,21] profile121_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node19
  · exact profile121_node20

def profile121_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node17 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28] 2 (by decide) (choices 3) [19] profile121_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22,28] (choices 3) [19] profile121_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile121_node18

def profile121_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node1 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22] 2 (by decide) (choices 3) [21,25,28] profile121_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [22] (choices 3) [21,25,28] profile121_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile121_node2
  · exact profile121_node13
  · exact profile121_node17

def profile121_node24_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 27 23 23 29 22), lower := (rows 27 23 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 26 22 22 28 16) }] }

theorem profile121_node24 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,21] 2 profile121_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,21] 2 profile121_node24_cert).mp (by decide +kernel))

def profile121_node25_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 27 23 23 30 21), lower := (rows 27 23 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 14 16), good := (rows 26 30 30 30 16) }] }

theorem profile121_node25 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,22] 2 profile121_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19,22] 2 profile121_node25_cert).mp (by decide +kernel))

def profile121_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node23 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19] 2 (by decide) (choices 3) [21,22] profile121_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21,19] (choices 3) [21,22] profile121_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node24
  · exact profile121_node25

def profile121_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node22 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21] 2 (by decide) (choices 3) [19] profile121_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26,21] (choices 3) [19] profile121_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile121_node23

def profile121_node21_route : Route 5 := (fun mask => (mask,id))

theorem profile121_node21 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26] 2 (by decide) (choices 3) [21] profile121_node21_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [26] (choices 3) [21] profile121_node21_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile121_node22

def profile121_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile121_node0 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [] 2 (by decide) (choices 3) [22,26] profile121_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [] (choices 3) [22,26] profile121_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile121_node1
  · exact profile121_node21

theorem profile121 : Upper (D (n:=5) [51,51,51,49,36]) (R (n:=5) [51,51,51,49,36]) [] 2 := profile121_node0

def profile122_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile122_node2 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,21] 2 profile122_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,21] 2 profile122_node2_cert).mp (by decide +kernel))

def profile122_node4_cert : CutBound 5 := { lost := (rows 8 0 8 2 2), upper := (rows 23 27 23 29 29), lower := (rows 23 27 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 23 23 23 0 16) }] }

theorem profile122_node4 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,19] 2 profile122_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,19] 2 profile122_node4_cert).mp (by decide +kernel))

def profile122_node6_cert : CutBound 5 := { lost := (rows 0 4 2 4 2), upper := (rows 23 27 29 27 21), lower := (rows 23 27 29 27 16), losses := [{ target := 1, region := (rows 1 0 14 8 31), good := (rows 21 29 29 29 16) },{ target := 2, region := (rows 1 15 0 15 16), good := (rows 27 27 27 27 16) }] }

theorem profile122_node6 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,19] 2 profile122_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,19] 2 profile122_node6_cert).mp (by decide +kernel))

def profile122_node7_cert : CutBound 5 := { lost := (rows 0 4 2 2 4), upper := (rows 23 27 29 29 19), lower := (rows 23 27 29 29 16), losses := [{ target := 1, region := (rows 1 0 15 15 16), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 14 0 8 31), good := (rows 19 27 27 27 16) }] }

theorem profile122_node7 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,21] 2 :=
  cut_bound_sound (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,21] 2 profile122_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25,21] 2 profile122_node7_cert).mp (by decide +kernel))

def profile122_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile122_node5 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25] 2 (by decide) (choices 3) [19,21] profile122_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25,25] (choices 3) [19,21] profile122_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile122_node6
  · exact profile122_node7

def profile122_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile122_node3 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25] 2 (by decide) (choices 3) [19,25] profile122_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22,25] (choices 3) [19,25] profile122_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile122_node4
  · exact profile122_node5

def profile122_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile122_node1 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22] 2 (by decide) (choices 3) [21,25] profile122_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [22] (choices 3) [21,25] profile122_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile122_node2
  · exact profile122_node3

def profile122_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile122_node0 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [] 2 := by
  apply routed_branch (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [] 2 (by decide) (choices 3) [22] profile122_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [] (choices 3) [22] profile122_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile122_node1

theorem profile122 : Upper (D (n:=5) [52,50,50,50,36]) (R (n:=5) [52,50,50,50,36]) [] 2 := profile122_node0

#print axioms profile122
end Delivery.FiveVertexPositive14
