import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile96_node3_cert : CutBound 5 := { lost := (rows 0 0 0 3 3), upper := (rows 31 31 7 28 28), lower := (rows 31 31 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile96_node3 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,3] 2 profile96_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,3] 2 profile96_node3_cert).mp (by decide +kernel))

def profile96_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 9), upper := (rows 31 31 13 30 22), lower := (rows 31 31 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile96_node4 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,9] 2 profile96_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,9] 2 profile96_node4_cert).mp (by decide +kernel))

def profile96_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 10), upper := (rows 31 31 14 29 21), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile96_node5 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,10] 2 profile96_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,10] 2 profile96_node5_cert).mp (by decide +kernel))

def profile96_node6_cert : CutBound 5 := { lost := (rows 0 0 3 16 8), upper := (rows 31 31 28 15 23), lower := (rows 31 31 28 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile96_node6 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,24] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,24] 2 profile96_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29,24] 2 profile96_node6_cert).mp (by decide +kernel))

def profile96_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile96_node2 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29] 2 (by decide) (choices 2) [3,9,10,24] profile96_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30,29] (choices 2) [3,9,10,24] profile96_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile96_node3
  · exact profile96_node4
  · exact profile96_node5
  · exact profile96_node6

def profile96_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile96_node1 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30] 2 (by decide) (choices 4) [29] profile96_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [30] (choices 4) [29] profile96_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile96_node2

def profile96_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile96_node0 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [] 2 (by decide) (choices 4) [30] profile96_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [] (choices 4) [30] profile96_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile96_node1

theorem profile96 : Upper (D (n:=5) [66,66,36,35,35]) (R (n:=5) [66,66,36,35,35]) [] 2 := profile96_node0

def profile97_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 27 15 27 19), lower := (rows 31 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 19 23 0 16) }] }

theorem profile97_node3 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,11] 2 profile97_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,11] 2 profile97_node3_cert).mp (by decide +kernel))

def profile97_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 27 29 11 19), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile97_node4 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,25] 2 profile97_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25,25] 2 profile97_node4_cert).mp (by decide +kernel))

def profile97_node2_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile97_node2 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25] 2 (by decide) (choices 3) [11,25] profile97_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30,25] (choices 3) [11,25] profile97_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile97_node3
  · exact profile97_node4

def profile97_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node1 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30] 2 (by decide) (choices 3) [25] profile97_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [30] (choices 3) [25] profile97_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node2

def profile97_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile97_node0 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [] 2 (by decide) (choices 4) [30] profile97_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [] (choices 4) [30] profile97_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile97_node1

theorem profile97 : Upper (D (n:=5) [68,51,49,35,35]) (R (n:=5) [68,51,49,35,35]) [] 2 := profile97_node0

def profile98_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 27 15 27 19), lower := (rows 31 27 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 19 23 0 16) }] }

theorem profile98_node3 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,11] 2 profile98_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,11] 2 profile98_node3_cert).mp (by decide +kernel))

def profile98_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 27 30 11 19), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile98_node4 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,26] 2 profile98_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25,26] 2 profile98_node4_cert).mp (by decide +kernel))

def profile98_node2_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile98_node2 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25] 2 (by decide) (choices 3) [11,26] profile98_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30,25] (choices 3) [11,26] profile98_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile98_node3
  · exact profile98_node4

def profile98_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node1 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30] 2 (by decide) (choices 3) [25] profile98_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [30] (choices 3) [25] profile98_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node2

def profile98_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile98_node0 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [] 2 (by decide) (choices 4) [30] profile98_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [] (choices 4) [30] profile98_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile98_node1

theorem profile98 : Upper (D (n:=5) [67,52,49,35,35]) (R (n:=5) [67,52,49,35,35]) [] 2 := profile98_node0

def profile99_node3_cert : CutBound 5 := { lost := (rows 0 0 0 6 6), upper := (rows 31 15 23 25 25), lower := (rows 31 15 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile99_node3 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,19] 2 profile99_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,19] 2 profile99_node3_cert).mp (by decide +kernel))

def profile99_node4_cert : CutBound 5 := { lost := (rows 0 0 2 4 12), upper := (rows 31 15 29 27 19), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile99_node4 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,25] 2 profile99_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13,25] 2 profile99_node4_cert).mp (by decide +kernel))

def profile99_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node2 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13] 2 (by decide) (choices 3) [19,25] profile99_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,13] (choices 3) [19,25] profile99_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile99_node3
  · exact profile99_node4

def profile99_node6_cert : CutBound 5 := { lost := (rows 0 4 0 2 10), upper := (rows 31 27 15 29 21), lower := (rows 31 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile99_node6 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,11] 2 profile99_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,11] 2 profile99_node6_cert).mp (by decide +kernel))

def profile99_node7_cert : CutBound 5 := { lost := (rows 0 4 2 16 8), upper := (rows 31 27 29 15 23), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile99_node7 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,25] 2 profile99_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25,25] 2 profile99_node7_cert).mp (by decide +kernel))

def profile99_node5_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile99_node5 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25] 2 (by decide) (choices 3) [11,25] profile99_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30,25] (choices 3) [11,25] profile99_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile99_node6
  · exact profile99_node7

def profile99_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile99_node1 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30] 2 (by decide) (choices 3) [13,25] profile99_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [30] (choices 3) [13,25] profile99_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile99_node2
  · exact profile99_node5

def profile99_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile99_node0 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [] 2 (by decide) (choices 4) [30] profile99_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [] (choices 4) [30] profile99_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile99_node1

theorem profile99 : Upper (D (n:=5) [68,50,50,35,35]) (R (n:=5) [68,50,50,35,35]) [] 2 := profile99_node0

def profile100_node3_cert : CutBound 5 := { lost := (rows 0 16 8 4 4), upper := (rows 31 15 23 27 27), lower := (rows 31 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile100_node3 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,19] 2 profile100_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,19] 2 profile100_node3_cert).mp (by decide +kernel))

def profile100_node4_cert : CutBound 5 := { lost := (rows 0 0 2 4 12), upper := (rows 31 15 29 27 19), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile100_node4 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,25] 2 profile100_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,25] 2 profile100_node4_cert).mp (by decide +kernel))

def profile100_node5_cert : CutBound 5 := { lost := (rows 0 0 1 4 12), upper := (rows 31 15 30 27 19), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile100_node5 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,26] 2 profile100_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13,26] 2 profile100_node5_cert).mp (by decide +kernel))

def profile100_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile100_node2 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13] 2 (by decide) (choices 3) [19,25,26] profile100_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,13] (choices 3) [19,25,26] profile100_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile100_node3
  · exact profile100_node4
  · exact profile100_node5

def profile100_node8_cert : CutBound 5 := { lost := (rows 0 4 0 6 1), upper := (rows 31 27 15 25 22), lower := (rows 31 27 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 24 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 25 13 25 16) },{ target := 2, region := (rows 1 11 0 11 16), good := (rows 27 27 11 27 16) }] }

theorem profile100_node8 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,17] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,17] 2 profile100_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,17] 2 profile100_node8_cert).mp (by decide +kernel))

def profile100_node9_cert : CutBound 5 := { lost := (rows 0 4 0 5 2), upper := (rows 31 27 15 26 21), lower := (rows 31 27 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 26 14 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 24 16) },{ target := 2, region := (rows 1 3 0 11 16), good := (rows 27 27 11 26 16) }] }

theorem profile100_node9 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,18] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,18] 2 profile100_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,18] 2 profile100_node9_cert).mp (by decide +kernel))

def profile100_node10_cert : CutBound 5 := { lost := (rows 0 4 0 3 4), upper := (rows 31 27 15 28 19), lower := (rows 31 27 15 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 26 14 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 25 13 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) }] }

theorem profile100_node10 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,20] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,20] 2 profile100_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11,20] 2 profile100_node10_cert).mp (by decide +kernel))

def profile100_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile100_node7 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11] 2 (by decide) (choices 2) [17,18,20] profile100_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,11] (choices 2) [17,18,20] profile100_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile100_node8
  · exact profile100_node9
  · exact profile100_node10

def profile100_node11_cert : CutBound 5 := { lost := (rows 0 4 2 16 8), upper := (rows 31 27 29 15 23), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 13 8 0) }] }

theorem profile100_node11 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,25] 2 profile100_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,25] 2 profile100_node11_cert).mp (by decide +kernel))

def profile100_node12_cert : CutBound 5 := { lost := (rows 0 4 1 16 8), upper := (rows 31 27 30 15 23), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 14 8 0) }] }

theorem profile100_node12 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,26] 2 profile100_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25,26] 2 profile100_node12_cert).mp (by decide +kernel))

def profile100_node6_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile100_node6 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile100_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,25] (choices 3) [11,25,26] profile100_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile100_node7
  · exact profile100_node11
  · exact profile100_node12

def profile100_node14_cert : CutBound 5 := { lost := (rows 0 1 0 4 12), upper := (rows 31 30 15 27 19), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile100_node14 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,11] 2 profile100_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,11] 2 profile100_node14_cert).mp (by decide +kernel))

def profile100_node15_cert : CutBound 5 := { lost := (rows 0 1 2 4 4), upper := (rows 31 30 29 11 19), lower := (rows 31 30 29 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) }] }

theorem profile100_node15 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,25] 2 profile100_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28,25] 2 profile100_node15_cert).mp (by decide +kernel))

def profile100_node13_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile100_node13 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28] 2 (by decide) (choices 3) [11,25] profile100_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30,28] (choices 3) [11,25] profile100_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile100_node14
  · exact profile100_node15

def profile100_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile100_node1 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile100_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [30] (choices 3) [13,25,28] profile100_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile100_node2
  · exact profile100_node6
  · exact profile100_node13

def profile100_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile100_node0 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [] 2 (by decide) (choices 4) [30] profile100_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [] (choices 4) [30] profile100_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile100_node1

theorem profile100 : Upper (D (n:=5) [67,51,50,35,35]) (R (n:=5) [67,51,50,35,35]) [] 2 := profile100_node0

def profile101_node3_cert : CutBound 5 := { lost := (rows 0 0 0 5 5), upper := (rows 31 15 23 26 26), lower := (rows 31 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile101_node3 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,19] 2 profile101_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,19] 2 profile101_node3_cert).mp (by decide +kernel))

def profile101_node4_cert : CutBound 5 := { lost := (rows 0 0 1 4 12), upper := (rows 31 15 30 27 19), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile101_node4 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,26] 2 profile101_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13,26] 2 profile101_node4_cert).mp (by decide +kernel))

def profile101_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile101_node2 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13] 2 (by decide) (choices 3) [19,26] profile101_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,13] (choices 3) [19,26] profile101_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile101_node3
  · exact profile101_node4

def profile101_node6_cert : CutBound 5 := { lost := (rows 0 4 0 1 9), upper := (rows 31 27 15 30 22), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile101_node6 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,11] 2 profile101_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,11] 2 profile101_node6_cert).mp (by decide +kernel))

def profile101_node7_cert : CutBound 5 := { lost := (rows 0 4 1 16 8), upper := (rows 31 27 30 15 23), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 14 8 0) }] }

theorem profile101_node7 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,26] 2 profile101_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25,26] 2 profile101_node7_cert).mp (by decide +kernel))

def profile101_node5_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile101_node5 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25] 2 (by decide) (choices 3) [11,26] profile101_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,25] (choices 3) [11,26] profile101_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile101_node6
  · exact profile101_node7

def profile101_node9_cert : CutBound 5 := { lost := (rows 0 1 0 4 12), upper := (rows 31 30 15 27 19), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 0 16) }] }

theorem profile101_node9 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,11] 2 profile101_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,11] 2 profile101_node9_cert).mp (by decide +kernel))

def profile101_node10_cert : CutBound 5 := { lost := (rows 0 1 1 4 4), upper := (rows 31 30 30 11 19), lower := (rows 31 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 26 8 16) }] }

theorem profile101_node10 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,26] 2 profile101_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28,26] 2 profile101_node10_cert).mp (by decide +kernel))

def profile101_node8_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile101_node8 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28] 2 (by decide) (choices 3) [11,26] profile101_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30,28] (choices 3) [11,26] profile101_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile101_node9
  · exact profile101_node10

def profile101_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile101_node1 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile101_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [30] (choices 3) [13,25,28] profile101_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile101_node2
  · exact profile101_node5
  · exact profile101_node8

def profile101_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile101_node0 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [] 2 (by decide) (choices 4) [30] profile101_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [] (choices 4) [30] profile101_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile101_node1

theorem profile101 : Upper (D (n:=5) [66,52,50,35,35]) (R (n:=5) [66,52,50,35,35]) [] 2 := profile101_node0

def profile102_node3_cert : CutBound 5 := { lost := (rows 0 16 8 1 1), upper := (rows 31 15 23 30 30), lower := (rows 31 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile102_node3 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,19] 2 profile102_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,19] 2 profile102_node3_cert).mp (by decide +kernel))

def profile102_node4_cert : CutBound 5 := { lost := (rows 0 0 2 1 9), upper := (rows 31 15 29 30 22), lower := (rows 31 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile102_node4 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,25] 2 profile102_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,25] 2 profile102_node4_cert).mp (by decide +kernel))

def profile102_node6_cert : CutBound 5 := { lost := (rows 0 0 1 6 1), upper := (rows 31 15 30 25 22), lower := (rows 31 15 30 25 16), losses := [{ target := 0, region := (rows 0 2 7 8 23), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 28 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 26 25 16) }] }

theorem profile102_node6 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,17] 2 profile102_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,17] 2 profile102_node6_cert).mp (by decide +kernel))

def profile102_node7_cert : CutBound 5 := { lost := (rows 0 0 1 5 2), upper := (rows 31 15 30 26 21), lower := (rows 31 15 30 26 16), losses := [{ target := 0, region := (rows 0 2 13 13 16), good := (rows 30 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 28 24 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 11 26 26 16) }] }

theorem profile102_node7 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,18] 2 profile102_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,18] 2 profile102_node7_cert).mp (by decide +kernel))

def profile102_node8_cert : CutBound 5 := { lost := (rows 0 0 1 3 4), upper := (rows 31 15 30 28 19), lower := (rows 31 15 30 28 16), losses := [{ target := 0, region := (rows 0 2 5 13 16), good := (rows 30 14 30 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 13 28 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 26 24 16) }] }

theorem profile102_node8 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,20] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,20] 2 profile102_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26,20] 2 profile102_node8_cert).mp (by decide +kernel))

def profile102_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node5 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26] 2 (by decide) (choices 2) [17,18,20] profile102_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13,26] (choices 2) [17,18,20] profile102_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node6
  · exact profile102_node7
  · exact profile102_node8

def profile102_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node2 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13] 2 (by decide) (choices 3) [19,25,26] profile102_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,13] (choices 3) [19,25,26] profile102_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node3
  · exact profile102_node4
  · exact profile102_node5

def profile102_node10_cert : CutBound 5 := { lost := (rows 0 4 0 1 9), upper := (rows 31 27 15 30 22), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile102_node10 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,11] 2 profile102_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,11] 2 profile102_node10_cert).mp (by decide +kernel))

def profile102_node11_cert : CutBound 5 := { lost := (rows 0 4 2 1 1), upper := (rows 31 27 29 14 22), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile102_node11 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,25] 2 profile102_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,25] 2 profile102_node11_cert).mp (by decide +kernel))

def profile102_node12_cert : CutBound 5 := { lost := (rows 0 4 1 16 8), upper := (rows 31 27 30 15 23), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 22 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 11 14 8 0) }] }

theorem profile102_node12 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,26] 2 profile102_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25,26] 2 profile102_node12_cert).mp (by decide +kernel))

def profile102_node9_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile102_node9 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile102_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,25] (choices 3) [11,25,26] profile102_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node10
  · exact profile102_node11
  · exact profile102_node12

def profile102_node15_cert : CutBound 5 := { lost := (rows 0 1 0 6 1), upper := (rows 31 30 15 25 22), lower := (rows 31 30 15 25 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 28 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 26 11 25 16) }] }

theorem profile102_node15 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,17] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,17] 2 profile102_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,17] 2 profile102_node15_cert).mp (by decide +kernel))

def profile102_node16_cert : CutBound 5 := { lost := (rows 0 1 0 5 2), upper := (rows 31 30 15 26 21), lower := (rows 31 30 15 26 16), losses := [{ target := 0, region := (rows 0 3 4 11 16), good := (rows 30 30 14 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 29 24 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 26 11 26 16) }] }

theorem profile102_node16 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,18] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,18] 2 profile102_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,18] 2 profile102_node16_cert).mp (by decide +kernel))

def profile102_node17_cert : CutBound 5 := { lost := (rows 0 1 0 3 4), upper := (rows 31 30 15 28 19), lower := (rows 31 30 15 28 16), losses := [{ target := 0, region := (rows 0 11 4 11 16), good := (rows 30 30 14 30 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 28 13 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 27 24 16) }] }

theorem profile102_node17 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,20] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,20] 2 profile102_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11,20] 2 profile102_node17_cert).mp (by decide +kernel))

def profile102_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node14 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11] 2 (by decide) (choices 2) [17,18,20] profile102_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,11] (choices 2) [17,18,20] profile102_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node15
  · exact profile102_node16
  · exact profile102_node17

def profile102_node18_cert : CutBound 5 := { lost := (rows 0 1 2 16 8), upper := (rows 31 30 29 15 23), lower := (rows 31 30 29 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 14 13 8 0) }] }

theorem profile102_node18 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,25] 2 profile102_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,25] 2 profile102_node18_cert).mp (by decide +kernel))

def profile102_node19_cert : CutBound 5 := { lost := (rows 0 1 1 16 8), upper := (rows 31 30 30 15 23), lower := (rows 31 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 22 0 16) },{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile102_node19 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,26] 2 profile102_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28,26] 2 profile102_node19_cert).mp (by decide +kernel))

def profile102_node13_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile102_node13 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28] 2 (by decide) (choices 3) [11,25,26] profile102_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30,28] (choices 3) [11,25,26] profile102_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node14
  · exact profile102_node18
  · exact profile102_node19

def profile102_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile102_node1 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile102_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [30] (choices 3) [13,25,28] profile102_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile102_node2
  · exact profile102_node9
  · exact profile102_node13

def profile102_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile102_node0 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [] 2 (by decide) (choices 4) [30] profile102_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [] (choices 4) [30] profile102_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile102_node1

theorem profile102 : Upper (D (n:=5) [66,51,51,35,35]) (R (n:=5) [66,51,51,35,35]) [] 2 := profile102_node0

def profile103_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile103_node2 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,13] 2 profile103_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,13] 2 profile103_node2_cert).mp (by decide +kernel))

def profile103_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 30 30 30), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile103_node3 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,25] 2 profile103_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,25] 2 profile103_node3_cert).mp (by decide +kernel))

def profile103_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 30 15 30 22), lower := (rows 31 30 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 22 23 0 16) }] }

theorem profile103_node5 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,11] 2 profile103_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,11] 2 profile103_node5_cert).mp (by decide +kernel))

def profile103_node6_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 30 30 15 23), lower := (rows 31 30 30 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 22 0 16) }] }

theorem profile103_node6 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,26] 2 profile103_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28,26] 2 profile103_node6_cert).mp (by decide +kernel))

def profile103_node4_route : Route 5 := (fun mask => match mask with | 19 => (11,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile103_node4 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28] 2 (by decide) (choices 3) [11,26] profile103_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30,28] (choices 3) [11,26] profile103_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile103_node5
  · exact profile103_node6

def profile103_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile103_node1 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile103_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [30] (choices 3) [13,25,28] profile103_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile103_node2
  · exact profile103_node3
  · exact profile103_node4

def profile103_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile103_node0 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [] 2 (by decide) (choices 4) [30] profile103_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [] (choices 4) [30] profile103_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile103_node1

theorem profile103 : Upper (D (n:=5) [65,52,51,35,35]) (R (n:=5) [65,52,51,35,35]) [] 2 := profile103_node0

def profile104_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 31 13 28 28), lower := (rows 31 31 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 28 8 16) }] }

theorem profile104_node3 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,9] 2 profile104_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,9] 2 profile104_node3_cert).mp (by decide +kernel))

def profile104_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 28 13 29), lower := (rows 31 31 28 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 28 8 16) }] }

theorem profile104_node4 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,24] 2 :=
  cut_bound_sound (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,24] 2 profile104_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29,24] 2 profile104_node4_cert).mp (by decide +kernel))

def profile104_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node2 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29] 2 (by decide) (choices 2) [9,24] profile104_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30,29] (choices 2) [9,24] profile104_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile104_node3
  · exact profile104_node4

def profile104_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node1 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30] 2 (by decide) (choices 4) [29] profile104_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [30] (choices 4) [29] profile104_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node2

def profile104_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile104_node0 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [] 2 (by decide) (choices 4) [30] profile104_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [] (choices 4) [30] profile104_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile104_node1

theorem profile104 : Upper (D (n:=5) [66,65,36,36,35]) (R (n:=5) [66,65,36,36,35]) [] 2 := profile104_node0

def profile105_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 2), upper := (rows 31 27 15 25 25), lower := (rows 31 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 25 29 8 16) }] }

theorem profile105_node3 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,11] 2 profile105_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,11] 2 profile105_node3_cert).mp (by decide +kernel))

def profile105_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 27 29 11 27), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile105_node4 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,25] 2 profile105_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25,25] 2 profile105_node4_cert).mp (by decide +kernel))

def profile105_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node2 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25] 2 (by decide) (choices 3) [11,25] profile105_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30,25] (choices 3) [11,25] profile105_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile105_node3
  · exact profile105_node4

def profile105_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node1 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30] 2 (by decide) (choices 3) [25] profile105_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [30] (choices 3) [25] profile105_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node2

def profile105_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile105_node0 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [] 2 (by decide) (choices 4) [30] profile105_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [] (choices 4) [30] profile105_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile105_node1

theorem profile105 : Upper (D (n:=5) [68,50,49,36,35]) (R (n:=5) [68,50,49,36,35]) [] 2 := profile105_node0

def profile106_node3_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 31 27 15 27 27), lower := (rows 31 27 15 8 16), losses := [{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile106_node3 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,11] 2 profile106_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,11] 2 profile106_node3_cert).mp (by decide +kernel))

def profile106_node4_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 27 29 11 27), lower := (rows 31 27 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile106_node4 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,25] 2 profile106_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,25] 2 profile106_node4_cert).mp (by decide +kernel))

def profile106_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 27 30 11 27), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile106_node5 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,26] 2 profile106_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25,26] 2 profile106_node5_cert).mp (by decide +kernel))

def profile106_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node2 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile106_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30,25] (choices 3) [11,25,26] profile106_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile106_node3
  · exact profile106_node4
  · exact profile106_node5

def profile106_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node1 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30] 2 (by decide) (choices 3) [25] profile106_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [30] (choices 3) [25] profile106_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile106_node2

def profile106_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile106_node0 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [] 2 (by decide) (choices 4) [30] profile106_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [] (choices 4) [30] profile106_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile106_node1

theorem profile106 : Upper (D (n:=5) [67,51,49,36,35]) (R (n:=5) [67,51,49,36,35]) [] 2 := profile106_node0

def profile107_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 27 15 26 26), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 26 30 8 16) }] }

theorem profile107_node3 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,11] 2 profile107_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,11] 2 profile107_node3_cert).mp (by decide +kernel))

def profile107_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 27 30 11 27), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile107_node4 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,26] 2 profile107_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25,26] 2 profile107_node4_cert).mp (by decide +kernel))

def profile107_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node2 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25] 2 (by decide) (choices 3) [11,26] profile107_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30,25] (choices 3) [11,26] profile107_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile107_node3
  · exact profile107_node4

def profile107_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node1 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30] 2 (by decide) (choices 3) [25] profile107_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [30] (choices 3) [25] profile107_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node2

def profile107_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile107_node0 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [] 2 (by decide) (choices 4) [30] profile107_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [] (choices 4) [30] profile107_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile107_node1

theorem profile107 : Upper (D (n:=5) [66,52,49,36,35]) (R (n:=5) [66,52,49,36,35]) [] 2 := profile107_node0

def profile108_node3_cert : CutBound 5 := { lost := (rows 0 16 2 4 4), upper := (rows 31 15 29 27 27), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 4, region := (rows 1 7 4 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile108_node3 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,25] 2 profile108_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,25] 2 profile108_node3_cert).mp (by decide +kernel))

def profile108_node4_cert : CutBound 5 := { lost := (rows 0 0 1 6 6), upper := (rows 31 15 30 25 25), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) }] }

theorem profile108_node4 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,26] 2 profile108_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13,26] 2 profile108_node4_cert).mp (by decide +kernel))

def profile108_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node2 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13] 2 (by decide) (choices 3) [25,26] profile108_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,13] (choices 3) [25,26] profile108_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node3
  · exact profile108_node4

def profile108_node6_cert : CutBound 5 := { lost := (rows 0 4 16 2 2), upper := (rows 31 27 15 29 29), lower := (rows 31 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile108_node6 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,11] 2 profile108_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,11] 2 profile108_node6_cert).mp (by decide +kernel))

def profile108_node8_cert : CutBound 5 := { lost := (rows 0 4 2 4 3), upper := (rows 31 27 29 11 28), lower := (rows 31 27 29 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 15 8 31), good := (rows 29 29 29 29 16) },{ target := 2, region := (rows 1 7 0 15 16), good := (rows 27 27 27 11 16) }] }

theorem profile108_node8 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,3] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,3] 2 profile108_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,3] 2 profile108_node8_cert).mp (by decide +kernel))

def profile108_node9_cert : CutBound 5 := { lost := (rows 0 4 2 2 5), upper := (rows 31 27 29 13 26), lower := (rows 31 27 29 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 7 15 16), good := (rows 29 29 29 13 16) },{ target := 2, region := (rows 1 15 0 8 31), good := (rows 27 27 27 27 16) }] }

theorem profile108_node9 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,5] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,5] 2 profile108_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,5] 2 profile108_node9_cert).mp (by decide +kernel))

def profile108_node10_cert : CutBound 5 := { lost := (rows 0 4 2 1 6), upper := (rows 31 27 29 14 25), lower := (rows 31 27 29 14 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 26 28 14 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) }] }

theorem profile108_node10 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,6] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,6] 2 profile108_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25,6] 2 profile108_node10_cert).mp (by decide +kernel))

def profile108_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node7 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25] 2 (by decide) (choices 2) [3,5,6] profile108_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,25] (choices 2) [3,5,6] profile108_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node8
  · exact profile108_node9
  · exact profile108_node10

def profile108_node11_cert : CutBound 5 := { lost := (rows 0 4 1 2 2), upper := (rows 31 27 30 13 29), lower := (rows 31 27 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 28 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 26 8 16) }] }

theorem profile108_node11 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,26] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,26] 2 profile108_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25,26] 2 profile108_node11_cert).mp (by decide +kernel))

def profile108_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node5 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile108_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,25] (choices 3) [11,25,26] profile108_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node6
  · exact profile108_node7
  · exact profile108_node11

def profile108_node13_cert : CutBound 5 := { lost := (rows 0 1 0 6 6), upper := (rows 31 30 15 25 25), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) }] }

theorem profile108_node13 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,11] 2 profile108_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,11] 2 profile108_node13_cert).mp (by decide +kernel))

def profile108_node14_cert : CutBound 5 := { lost := (rows 0 1 2 4 4), upper := (rows 31 30 29 11 27), lower := (rows 31 30 29 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) }] }

theorem profile108_node14 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,25] 2 profile108_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28,25] 2 profile108_node14_cert).mp (by decide +kernel))

def profile108_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node12 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28] 2 (by decide) (choices 3) [11,25] profile108_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30,28] (choices 3) [11,25] profile108_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile108_node13
  · exact profile108_node14

def profile108_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node1 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile108_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [30] (choices 3) [13,25,28] profile108_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile108_node2
  · exact profile108_node5
  · exact profile108_node12

def profile108_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile108_node0 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [] 2 (by decide) (choices 4) [30] profile108_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [] (choices 4) [30] profile108_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile108_node1

theorem profile108 : Upper (D (n:=5) [67,50,50,36,35]) (R (n:=5) [67,50,50,36,35]) [] 2 := profile108_node0

def profile109_node3_cert : CutBound 5 := { lost := (rows 0 0 2 5 5), upper := (rows 31 15 29 26 26), lower := (rows 31 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) }] }

theorem profile109_node3 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,25] 2 profile109_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,25] 2 profile109_node3_cert).mp (by decide +kernel))

def profile109_node4_cert : CutBound 5 := { lost := (rows 0 16 1 4 4), upper := (rows 31 15 30 27 27), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 14 8 0) }] }

theorem profile109_node4 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,26] 2 profile109_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13,26] 2 profile109_node4_cert).mp (by decide +kernel))

def profile109_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node2 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13] 2 (by decide) (choices 3) [25,26] profile109_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,13] (choices 3) [25,26] profile109_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile109_node3
  · exact profile109_node4

def profile109_node6_cert : CutBound 5 := { lost := (rows 0 4 16 1 1), upper := (rows 31 27 15 30 30), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile109_node6 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,11] 2 profile109_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,11] 2 profile109_node6_cert).mp (by decide +kernel))

def profile109_node7_cert : CutBound 5 := { lost := (rows 0 4 2 1 1), upper := (rows 31 27 29 14 30), lower := (rows 31 27 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 7 0 8 16), good := (rows 27 27 27 8 16) }] }

theorem profile109_node7 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,25] 2 profile109_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,25] 2 profile109_node7_cert).mp (by decide +kernel))

def profile109_node9_cert : CutBound 5 := { lost := (rows 0 4 1 4 3), upper := (rows 31 27 30 11 28), lower := (rows 31 27 30 11 16), losses := [{ target := 0, region := (rows 0 2 15 8 31), good := (rows 30 30 30 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 28 25 16) },{ target := 2, region := (rows 1 3 0 11 16), good := (rows 27 27 26 11 16) }] }

theorem profile109_node9 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,3] 2 profile109_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,3] 2 profile109_node9_cert).mp (by decide +kernel))

def profile109_node10_cert : CutBound 5 := { lost := (rows 0 4 1 2 5), upper := (rows 31 27 30 13 26), lower := (rows 31 27 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 23), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 25 28 13 16) },{ target := 2, region := (rows 1 11 0 8 31), good := (rows 27 27 26 27 16) }] }

theorem profile109_node10 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,5] 2 profile109_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,5] 2 profile109_node10_cert).mp (by decide +kernel))

def profile109_node11_cert : CutBound 5 := { lost := (rows 0 4 1 1 6), upper := (rows 31 27 30 14 25), lower := (rows 31 27 30 14 16), losses := [{ target := 0, region := (rows 0 2 7 15 16), good := (rows 30 30 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 25 28 28 16) },{ target := 2, region := (rows 1 3 0 8 19), good := (rows 27 27 26 26 16) }] }

theorem profile109_node11 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,6] 2 profile109_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26,6] 2 profile109_node11_cert).mp (by decide +kernel))

def profile109_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node8 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26] 2 (by decide) (choices 2) [3,5,6] profile109_node8_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25,26] (choices 2) [3,5,6] profile109_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile109_node9
  · exact profile109_node10
  · exact profile109_node11

def profile109_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node5 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25] 2 (by decide) (choices 3) [11,25,26] profile109_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,25] (choices 3) [11,25,26] profile109_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile109_node6
  · exact profile109_node7
  · exact profile109_node8

def profile109_node13_cert : CutBound 5 := { lost := (rows 0 1 16 4 4), upper := (rows 31 30 15 27 27), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 2, region := (rows 1 2 0 13 21), good := (rows 27 26 27 8 16) },{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile109_node13 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,11] 2 profile109_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,11] 2 profile109_node13_cert).mp (by decide +kernel))

def profile109_node14_cert : CutBound 5 := { lost := (rows 0 1 2 4 4), upper := (rows 31 30 29 11 27), lower := (rows 31 30 29 8 16), losses := [{ target := 0, region := (rows 0 7 4 8 16), good := (rows 30 30 30 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 25 8 16) }] }

theorem profile109_node14 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,25] 2 profile109_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,25] 2 profile109_node14_cert).mp (by decide +kernel))

def profile109_node15_cert : CutBound 5 := { lost := (rows 0 1 1 4 4), upper := (rows 31 30 30 11 27), lower := (rows 31 30 30 8 16), losses := [{ target := 0, region := (rows 0 7 7 8 16), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 26 8 16) }] }

theorem profile109_node15 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,26] 2 profile109_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28,26] 2 profile109_node15_cert).mp (by decide +kernel))

def profile109_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node12 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28] 2 (by decide) (choices 3) [11,25,26] profile109_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30,28] (choices 3) [11,25,26] profile109_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile109_node13
  · exact profile109_node14
  · exact profile109_node15

def profile109_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node1 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile109_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [30] (choices 3) [13,25,28] profile109_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile109_node2
  · exact profile109_node5
  · exact profile109_node12

def profile109_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile109_node0 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [] 2 (by decide) (choices 4) [30] profile109_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [] (choices 4) [30] profile109_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile109_node1

theorem profile109 : Upper (D (n:=5) [66,51,50,36,35]) (R (n:=5) [66,51,50,36,35]) [] 2 := profile109_node0

def profile110_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 15 30 26 26), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile110_node2 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,13] 2 profile110_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,13] 2 profile110_node2_cert).mp (by decide +kernel))

def profile110_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 30 30 30), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile110_node3 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,25] 2 profile110_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,25] 2 profile110_node3_cert).mp (by decide +kernel))

def profile110_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 30 31 27 27), lower := (rows 31 30 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) }] }

theorem profile110_node4 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,28] 2 profile110_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30,28] 2 profile110_node4_cert).mp (by decide +kernel))

def profile110_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile110_node1 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile110_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [30] (choices 3) [13,25,28] profile110_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile110_node2
  · exact profile110_node3
  · exact profile110_node4

def profile110_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile110_node0 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [] 2 (by decide) (choices 4) [30] profile110_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [] (choices 4) [30] profile110_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile110_node1

theorem profile110 : Upper (D (n:=5) [65,52,50,36,35]) (R (n:=5) [65,52,50,36,35]) [] 2 := profile110_node0

def profile111_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile111_node2 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,13] 2 profile111_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,13] 2 profile111_node2_cert).mp (by decide +kernel))

def profile111_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 30 30 30), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile111_node3 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,25] 2 profile111_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,25] 2 profile111_node3_cert).mp (by decide +kernel))

def profile111_node5_cert : CutBound 5 := { lost := (rows 0 0 16 0 0), upper := (rows 31 30 15 30 30), lower := (rows 31 30 15 8 16), losses := [{ target := 4, region := (rows 1 2 5 8 0), good := (rows 15 14 15 8 0) }] }

theorem profile111_node5 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,11] 2 profile111_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,11] 2 profile111_node5_cert).mp (by decide +kernel))

def profile111_node6_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 30 29 14 30), lower := (rows 31 30 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 28 29 8 16) }] }

theorem profile111_node6 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,25] 2 :=
  cut_bound_sound (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,25] 2 profile111_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,25] 2 profile111_node6_cert).mp (by decide +kernel))

def profile111_node7_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 31 30 30 15 31), lower := (rows 31 30 30 8 16), losses := [{ target := 4, region := (rows 1 2 4 9 0), good := (rows 15 14 14 8 0) }] }

theorem profile111_node7 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,26] 2 :=
  cut_bound_sound (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,26] 2 profile111_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28,26] 2 profile111_node7_cert).mp (by decide +kernel))

def profile111_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile111_node4 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28] 2 (by decide) (choices 3) [11,25,26] profile111_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30,28] (choices 3) [11,25,26] profile111_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile111_node5
  · exact profile111_node6
  · exact profile111_node7

def profile111_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile111_node1 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30] 2 (by decide) (choices 3) [13,25,28] profile111_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [30] (choices 3) [13,25,28] profile111_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile111_node2
  · exact profile111_node3
  · exact profile111_node4

def profile111_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile111_node0 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [] 2 := by
  apply routed_branch (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [] 2 (by decide) (choices 4) [30] profile111_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [] (choices 4) [30] profile111_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile111_node1

theorem profile111 : Upper (D (n:=5) [65,51,51,36,35]) (R (n:=5) [65,51,51,36,35]) [] 2 := profile111_node0

def profile112_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 15 23 23 27 19), lower := (rows 15 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile112_node2 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14,21] 2 profile112_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14,21] 2 profile112_node2_cert).mp (by decide +kernel))

def profile112_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node1 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14] 2 (by decide) (choices 3) [21] profile112_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [14] (choices 3) [21] profile112_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile112_node2

def profile112_node4_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 23 15 23 27 19), lower := (rows 23 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile112_node4 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,13] 2 profile112_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,13] 2 profile112_node4_cert).mp (by decide +kernel))

def profile112_node5_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 23 23 31 27 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile112_node5 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,21] 2 profile112_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,21] 2 profile112_node5_cert).mp (by decide +kernel))

def profile112_node7_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 27 23 15 23), lower := (rows 23 27 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile112_node7 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25,19] 2 profile112_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25,19] 2 profile112_node7_cert).mp (by decide +kernel))

def profile112_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node6 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25] 2 (by decide) (choices 3) [19] profile112_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22,25] (choices 3) [19] profile112_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile112_node7

def profile112_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node3 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22] 2 (by decide) (choices 3) [13,21,25] profile112_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [22] (choices 3) [13,21,25] profile112_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile112_node4
  · exact profile112_node5
  · exact profile112_node6

def profile112_node10_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 27 23 23 15 23), lower := (rows 27 23 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile112_node10 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21,19] 2 profile112_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21,19] 2 profile112_node10_cert).mp (by decide +kernel))

def profile112_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node9 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21] 2 (by decide) (choices 3) [19] profile112_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26,21] (choices 3) [19] profile112_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile112_node10

def profile112_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node8 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26] 2 (by decide) (choices 3) [21] profile112_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [26] (choices 3) [21] profile112_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile112_node9

def profile112_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile112_node0 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [] 2 (by decide) (choices 3) [14,22,26] profile112_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [] (choices 3) [14,22,26] profile112_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile112_node1
  · exact profile112_node3
  · exact profile112_node8

theorem profile112 : Upper (D (n:=5) [52,52,50,49,35]) (R (n:=5) [52,52,50,49,35]) [] 2 := profile112_node0

def profile113_node4_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 15 23 23 27 21), lower := (rows 15 23 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 21 21 25 16) }] }

theorem profile113_node4 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,19] 2 profile113_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,19] 2 profile113_node4_cert).mp (by decide +kernel))

def profile113_node5_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 15 23 23 29 19), lower := (rows 15 23 23 29 16), losses := [{ target := 1, region := (rows 1 0 4 14 16), good := (rows 13 29 29 29 16) }] }

theorem profile113_node5 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,21] 2 profile113_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19,21] 2 profile113_node5_cert).mp (by decide +kernel))

def profile113_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node3 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19] 2 (by decide) (choices 3) [19,21] profile113_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21,19] (choices 3) [19,21] profile113_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile113_node4
  · exact profile113_node5

def profile113_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node2 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21] 2 (by decide) (choices 3) [19] profile113_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14,21] (choices 3) [19] profile113_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node3

def profile113_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node1 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14] 2 (by decide) (choices 3) [21] profile113_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [14] (choices 3) [21] profile113_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node2

def profile113_node9_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 23 15 23 27 21), lower := (rows 23 15 23 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 23), good := (rows 21 29 21 25 16) }] }

theorem profile113_node9 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,19] 2 profile113_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,19] 2 profile113_node9_cert).mp (by decide +kernel))

def profile113_node10_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 15 23 29 19), lower := (rows 23 15 23 29 16), losses := [{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 13 29 29 16) }] }

theorem profile113_node10 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,21] 2 profile113_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19,21] 2 profile113_node10_cert).mp (by decide +kernel))

def profile113_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node8 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19] 2 (by decide) (choices 3) [19,21] profile113_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13,19] (choices 3) [19,21] profile113_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile113_node9
  · exact profile113_node10

def profile113_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node7 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13] 2 (by decide) (choices 3) [19] profile113_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,13] (choices 3) [19] profile113_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node8

def profile113_node13_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 23 23 15 27 21), lower := (rows 23 23 15 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 23), good := (rows 21 21 29 25 16) }] }

theorem profile113_node13 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,19] 2 profile113_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,19] 2 profile113_node13_cert).mp (by decide +kernel))

def profile113_node14_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 23 23 15 29 19), lower := (rows 23 23 15 29 16), losses := [{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 29 13 29 16) }] }

theorem profile113_node14 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,21] 2 profile113_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11,21] 2 profile113_node14_cert).mp (by decide +kernel))

def profile113_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node12 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11] 2 (by decide) (choices 3) [19,21] profile113_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,11] (choices 3) [19,21] profile113_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile113_node13
  · exact profile113_node14

def profile113_node15_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 23 23 15 31), lower := (rows 23 23 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile113_node15 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,19] 2 profile113_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,19] 2 profile113_node15_cert).mp (by decide +kernel))

def profile113_node16_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 23 29 15 23), lower := (rows 23 23 29 8 16), losses := [{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile113_node16 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,25] 2 profile113_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21,25] 2 profile113_node16_cert).mp (by decide +kernel))

def profile113_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node11 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21] 2 (by decide) (choices 3) [11,19,25] profile113_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,21] (choices 3) [11,19,25] profile113_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile113_node12
  · exact profile113_node15
  · exact profile113_node16

def profile113_node18_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 23 27 23 15 23), lower := (rows 23 27 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile113_node18 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25,19] 2 profile113_node18_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25,19] 2 profile113_node18_cert).mp (by decide +kernel))

def profile113_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node17 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25] 2 (by decide) (choices 3) [19] profile113_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22,25] (choices 3) [19] profile113_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node18

def profile113_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node6 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22] 2 (by decide) (choices 3) [13,21,25] profile113_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [22] (choices 3) [13,21,25] profile113_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile113_node7
  · exact profile113_node11
  · exact profile113_node17

def profile113_node21_cert : CutBound 5 := { lost := (rows 0 0 0 16 0), upper := (rows 27 23 23 15 23), lower := (rows 27 23 23 8 16), losses := [{ target := 4, region := (rows 1 2 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile113_node21 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21,19] 2 profile113_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21,19] 2 profile113_node21_cert).mp (by decide +kernel))

def profile113_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node20 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21] 2 (by decide) (choices 3) [19] profile113_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26,21] (choices 3) [19] profile113_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node21

def profile113_node19_route : Route 5 := (fun mask => (mask,id))

theorem profile113_node19 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26] 2 (by decide) (choices 3) [21] profile113_node19_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [26] (choices 3) [21] profile113_node19_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile113_node20

def profile113_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile113_node0 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [] 2 (by decide) (choices 3) [14,22,26] profile113_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [] (choices 3) [14,22,26] profile113_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile113_node1
  · exact profile113_node6
  · exact profile113_node19

theorem profile113 : Upper (D (n:=5) [52,51,51,49,35]) (R (n:=5) [52,51,51,49,35]) [] 2 := profile113_node0

#print axioms profile113
end Delivery.FiveVertexPositive14
