import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile79_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile79_node2 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,13] 2 profile79_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,13] 2 profile79_node2_cert).mp (by decide +kernel))

def profile79_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 14 14 30), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile79_node3 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,21] 2 profile79_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,21] 2 profile79_node3_cert).mp (by decide +kernel))

def profile79_node4_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile79_node4 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,28] 2 profile79_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30,28] 2 profile79_node4_cert).mp (by decide +kernel))

def profile79_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node1 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30] 2 (by decide) (choices 3) [13,21,28] profile79_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [30] (choices 3) [13,21,28] profile79_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile79_node2
  · exact profile79_node3
  · exact profile79_node4

def profile79_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile79_node0 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [] 2 (by decide) (choices 4) [30] profile79_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [] (choices 4) [30] profile79_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile79_node1

theorem profile79 : Upper (D (n:=5) [65,52,52,35,34]) (R (n:=5) [65,52,52,35,34]) [] 2 := profile79_node0

def profile80_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 13 13 29), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile80_node2 : Upper (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30,29] 2 profile80_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30,29] 2 profile80_node2_cert).mp (by decide +kernel))

def profile80_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node1 : Upper (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30] 2 (by decide) (choices 4) [29] profile80_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [30] (choices 4) [29] profile80_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node2

def profile80_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile80_node0 : Upper (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [] 2 (by decide) (choices 4) [30] profile80_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [] (choices 4) [30] profile80_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile80_node1

theorem profile80 : Upper (D (n:=5) [67,65,36,36,34]) (R (n:=5) [67,65,36,36,34]) [] 2 := profile80_node0

def profile81_node3_cert : CutBound 5 := { lost := (rows 0 0 18 17 1), upper := (rows 31 31 13 14 30), lower := (rows 31 31 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile81_node3 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,9] 2 profile81_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,9] 2 profile81_node3_cert).mp (by decide +kernel))

def profile81_node4_cert : CutBound 5 := { lost := (rows 0 0 17 18 2), upper := (rows 31 31 14 13 29), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile81_node4 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,10] 2 profile81_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29,10] 2 profile81_node4_cert).mp (by decide +kernel))

def profile81_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node2 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29] 2 (by decide) (choices 2) [9,10] profile81_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30,29] (choices 2) [9,10] profile81_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile81_node3
  · exact profile81_node4

def profile81_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node1 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30] 2 (by decide) (choices 4) [29] profile81_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [30] (choices 4) [29] profile81_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile81_node2

def profile81_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile81_node0 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [] 2 (by decide) (choices 4) [30] profile81_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [] (choices 4) [30] profile81_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile81_node1

theorem profile81 : Upper (D (n:=5) [66,66,36,36,34]) (R (n:=5) [66,66,36,36,34]) [] 2 := profile81_node0

def profile82_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 27 15 11 27), lower := (rows 31 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile82_node2 : Upper (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30,25] 2 profile82_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30,25] 2 profile82_node2_cert).mp (by decide +kernel))

def profile82_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node1 : Upper (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30] 2 (by decide) (choices 3) [25] profile82_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [30] (choices 3) [25] profile82_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile82_node2

def profile82_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile82_node0 : Upper (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [] 2 (by decide) (choices 4) [30] profile82_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [] (choices 4) [30] profile82_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile82_node1

theorem profile82 : Upper (D (n:=5) [68,51,49,36,34]) (R (n:=5) [68,51,49,36,34]) [] 2 := profile82_node0

def profile83_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 27 15 11 27), lower := (rows 31 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile83_node2 : Upper (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30,25] 2 profile83_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30,25] 2 profile83_node2_cert).mp (by decide +kernel))

def profile83_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node1 : Upper (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30] 2 (by decide) (choices 3) [25] profile83_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [30] (choices 3) [25] profile83_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node2

def profile83_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile83_node0 : Upper (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [] 2 (by decide) (choices 4) [30] profile83_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [] (choices 4) [30] profile83_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile83_node1

theorem profile83 : Upper (D (n:=5) [67,52,49,36,34]) (R (n:=5) [67,52,49,36,34]) [] 2 := profile83_node0

def profile84_node3_cert : CutBound 5 := { lost := (rows 0 0 0 6 6), upper := (rows 31 15 15 25 25), lower := (rows 31 15 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile84_node3 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,11] 2 profile84_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,11] 2 profile84_node3_cert).mp (by decide +kernel))

def profile84_node4_cert : CutBound 5 := { lost := (rows 0 16 2 20 4), upper := (rows 31 15 29 11 27), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile84_node4 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,25] 2 profile84_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13,25] 2 profile84_node4_cert).mp (by decide +kernel))

def profile84_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node2 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13] 2 (by decide) (choices 3) [11,25] profile84_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,13] (choices 3) [11,25] profile84_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node3
  · exact profile84_node4

def profile84_node6_cert : CutBound 5 := { lost := (rows 0 4 16 18 2), upper := (rows 31 27 15 13 29), lower := (rows 31 27 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 25 29 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile84_node6 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25,11] 2 profile84_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25,11] 2 profile84_node6_cert).mp (by decide +kernel))

def profile84_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node5 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25] 2 (by decide) (choices 3) [11] profile84_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30,25] (choices 3) [11] profile84_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node6

def profile84_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node1 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30] 2 (by decide) (choices 3) [13,25] profile84_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [30] (choices 3) [13,25] profile84_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile84_node2
  · exact profile84_node5

def profile84_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile84_node0 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [] 2 (by decide) (choices 4) [30] profile84_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [] (choices 4) [30] profile84_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile84_node1

theorem profile84 : Upper (D (n:=5) [68,50,50,36,34]) (R (n:=5) [68,50,50,36,34]) [] 2 := profile84_node0

def profile85_node3_cert : CutBound 5 := { lost := (rows 0 16 16 4 4), upper := (rows 31 15 15 27 27), lower := (rows 31 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile85_node3 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,11] 2 profile85_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,11] 2 profile85_node3_cert).mp (by decide +kernel))

def profile85_node4_cert : CutBound 5 := { lost := (rows 0 16 2 20 4), upper := (rows 31 15 29 11 27), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile85_node4 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,25] 2 profile85_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,25] 2 profile85_node4_cert).mp (by decide +kernel))

def profile85_node5_cert : CutBound 5 := { lost := (rows 0 16 1 20 4), upper := (rows 31 15 30 11 27), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile85_node5 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,26] 2 profile85_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13,26] 2 profile85_node5_cert).mp (by decide +kernel))

def profile85_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node2 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13] 2 (by decide) (choices 3) [11,25,26] profile85_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,13] (choices 3) [11,25,26] profile85_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node3
  · exact profile85_node4
  · exact profile85_node5

def profile85_node8_cert : CutBound 5 := { lost := (rows 0 4 0 4 3), upper := (rows 31 27 15 11 28), lower := (rows 31 27 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 26 30 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 25 29 25 16) },{ target := 2, region := (rows 1 3 0 15 16), good := (rows 27 27 11 11 16) }] }

theorem profile85_node8 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,3] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,3] 2 profile85_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,3] 2 profile85_node8_cert).mp (by decide +kernel))

def profile85_node9_cert : CutBound 5 := { lost := (rows 0 4 0 2 5), upper := (rows 31 27 15 13 26), lower := (rows 31 27 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 26 30 28 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 25 13 13 16) },{ target := 2, region := (rows 1 15 0 8 31), good := (rows 27 27 27 27 16) }] }

theorem profile85_node9 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,5] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,5] 2 profile85_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,5] 2 profile85_node9_cert).mp (by decide +kernel))

def profile85_node10_cert : CutBound 5 := { lost := (rows 0 4 0 1 6), upper := (rows 31 27 15 14 25), lower := (rows 31 27 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 13 16), good := (rows 30 26 14 14 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 25 29 28 16) },{ target := 2, region := (rows 1 7 0 8 23), good := (rows 27 27 27 26 16) }] }

theorem profile85_node10 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,6] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,6] 2 profile85_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11,6] 2 profile85_node10_cert).mp (by decide +kernel))

def profile85_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node7 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11] 2 (by decide) (choices 2) [3,5,6] profile85_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25,11] (choices 2) [3,5,6] profile85_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node8
  · exact profile85_node9
  · exact profile85_node10

def profile85_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node6 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25] 2 (by decide) (choices 3) [11] profile85_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,25] (choices 3) [11] profile85_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node7

def profile85_node11_cert : CutBound 5 := { lost := (rows 0 1 16 20 4), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile85_node11 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,28] 2 profile85_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30,28] 2 profile85_node11_cert).mp (by decide +kernel))

def profile85_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node1 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile85_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [30] (choices 3) [13,25,28] profile85_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile85_node2
  · exact profile85_node6
  · exact profile85_node11

def profile85_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile85_node0 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [] 2 (by decide) (choices 4) [30] profile85_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [] (choices 4) [30] profile85_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile85_node1

theorem profile85 : Upper (D (n:=5) [67,51,50,36,34]) (R (n:=5) [67,51,50,36,34]) [] 2 := profile85_node0

def profile86_node3_cert : CutBound 5 := { lost := (rows 0 0 0 5 5), upper := (rows 31 15 15 26 26), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) }] }

theorem profile86_node3 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,11] 2 profile86_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,11] 2 profile86_node3_cert).mp (by decide +kernel))

def profile86_node4_cert : CutBound 5 := { lost := (rows 0 16 1 20 4), upper := (rows 31 15 30 11 27), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile86_node4 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,26] 2 profile86_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13,26] 2 profile86_node4_cert).mp (by decide +kernel))

def profile86_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node2 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13] 2 (by decide) (choices 3) [11,26] profile86_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,13] (choices 3) [11,26] profile86_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile86_node3
  · exact profile86_node4

def profile86_node6_cert : CutBound 5 := { lost := (rows 0 4 16 17 1), upper := (rows 31 27 15 14 30), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile86_node6 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25,11] 2 profile86_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25,11] 2 profile86_node6_cert).mp (by decide +kernel))

def profile86_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node5 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25] 2 (by decide) (choices 3) [11] profile86_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,25] (choices 3) [11] profile86_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node6

def profile86_node7_cert : CutBound 5 := { lost := (rows 0 1 16 20 4), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile86_node7 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,28] 2 profile86_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30,28] 2 profile86_node7_cert).mp (by decide +kernel))

def profile86_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node1 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile86_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [30] (choices 3) [13,25,28] profile86_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile86_node2
  · exact profile86_node5
  · exact profile86_node7

def profile86_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile86_node0 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [] 2 (by decide) (choices 4) [30] profile86_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [] (choices 4) [30] profile86_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile86_node1

theorem profile86 : Upper (D (n:=5) [66,52,50,36,34]) (R (n:=5) [66,52,50,36,34]) [] 2 := profile86_node0

def profile87_node3_cert : CutBound 5 := { lost := (rows 0 16 16 1 1), upper := (rows 31 15 15 30 30), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile87_node3 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,11] 2 profile87_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,11] 2 profile87_node3_cert).mp (by decide +kernel))

def profile87_node4_cert : CutBound 5 := { lost := (rows 0 16 2 17 1), upper := (rows 31 15 29 14 30), lower := (rows 31 15 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile87_node4 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,25] 2 profile87_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,25] 2 profile87_node4_cert).mp (by decide +kernel))

def profile87_node6_cert : CutBound 5 := { lost := (rows 0 0 1 4 3), upper := (rows 31 15 30 11 28), lower := (rows 31 15 30 11 16), losses := [{ target := 0, region := (rows 0 2 15 8 31), good := (rows 30 30 30 30 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 28 25 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 11 26 11 16) }] }

theorem profile87_node6 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,3] 2 profile87_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,3] 2 profile87_node6_cert).mp (by decide +kernel))

def profile87_node7_cert : CutBound 5 := { lost := (rows 0 0 1 2 5), upper := (rows 31 15 30 13 26), lower := (rows 31 15 30 13 16), losses := [{ target := 0, region := (rows 0 2 7 8 23), good := (rows 30 30 30 28 16) },{ target := 1, region := (rows 1 0 4 11 16), good := (rows 29 13 28 13 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 26 25 16) }] }

theorem profile87_node7 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,5] 2 profile87_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,5] 2 profile87_node7_cert).mp (by decide +kernel))

def profile87_node8_cert : CutBound 5 := { lost := (rows 0 0 1 1 6), upper := (rows 31 15 30 14 25), lower := (rows 31 15 30 14 16), losses := [{ target := 0, region := (rows 0 2 5 15 16), good := (rows 30 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 28 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 26 26 16) }] }

theorem profile87_node8 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,6] 2 profile87_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26,6] 2 profile87_node8_cert).mp (by decide +kernel))

def profile87_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node5 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26] 2 (by decide) (choices 2) [3,5,6] profile87_node5_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13,26] (choices 2) [3,5,6] profile87_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node6
  · exact profile87_node7
  · exact profile87_node8

def profile87_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node2 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13] 2 (by decide) (choices 3) [11,25,26] profile87_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,13] (choices 3) [11,25,26] profile87_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node3
  · exact profile87_node4
  · exact profile87_node5

def profile87_node10_cert : CutBound 5 := { lost := (rows 0 4 16 17 1), upper := (rows 31 27 15 14 30), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile87_node10 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25,11] 2 profile87_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25,11] 2 profile87_node10_cert).mp (by decide +kernel))

def profile87_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node9 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25] 2 (by decide) (choices 3) [11] profile87_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,25] (choices 3) [11] profile87_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node10

def profile87_node13_cert : CutBound 5 := { lost := (rows 0 1 0 4 3), upper := (rows 31 30 15 11 28), lower := (rows 31 30 15 11 16), losses := [{ target := 0, region := (rows 0 7 4 8 23), good := (rows 30 30 30 26 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 28 29 25 16) },{ target := 2, region := (rows 1 2 0 13 16), good := (rows 27 26 11 11 16) }] }

theorem profile87_node13 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,3] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,3] 2 profile87_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,3] 2 profile87_node13_cert).mp (by decide +kernel))

def profile87_node14_cert : CutBound 5 := { lost := (rows 0 1 0 2 5), upper := (rows 31 30 15 13 26), lower := (rows 31 30 15 13 16), losses := [{ target := 0, region := (rows 0 15 4 8 31), good := (rows 30 30 30 30 16) },{ target := 1, region := (rows 1 0 4 13 16), good := (rows 29 28 13 13 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 26 27 25 16) }] }

theorem profile87_node14 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,5] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,5] 2 profile87_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,5] 2 profile87_node14_cert).mp (by decide +kernel))

def profile87_node15_cert : CutBound 5 := { lost := (rows 0 1 0 1 6), upper := (rows 31 30 15 14 25), lower := (rows 31 30 15 14 16), losses := [{ target := 0, region := (rows 0 3 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 29 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 27 26 16) }] }

theorem profile87_node15 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,6] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,6] 2 profile87_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11,6] 2 profile87_node15_cert).mp (by decide +kernel))

def profile87_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node12 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11] 2 (by decide) (choices 2) [3,5,6] profile87_node12_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28,11] (choices 2) [3,5,6] profile87_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node13
  · exact profile87_node14
  · exact profile87_node15

def profile87_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node11 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28] 2 (by decide) (choices 3) [11] profile87_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30,28] (choices 3) [11] profile87_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node12

def profile87_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node1 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile87_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [30] (choices 3) [13,25,28] profile87_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile87_node2
  · exact profile87_node9
  · exact profile87_node11

def profile87_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile87_node0 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [] 2 (by decide) (choices 4) [30] profile87_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [] (choices 4) [30] profile87_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile87_node1

theorem profile87 : Upper (D (n:=5) [66,51,51,36,34]) (R (n:=5) [66,51,51,36,34]) [] 2 := profile87_node0

def profile88_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 30 30 30), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile88_node2 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,13] 2 profile88_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,13] 2 profile88_node2_cert).mp (by decide +kernel))

def profile88_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 14 14 30), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile88_node3 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,25] 2 profile88_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,25] 2 profile88_node3_cert).mp (by decide +kernel))

def profile88_node4_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile88_node4 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,28] 2 profile88_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30,28] 2 profile88_node4_cert).mp (by decide +kernel))

def profile88_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node1 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile88_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [30] (choices 3) [13,25,28] profile88_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile88_node2
  · exact profile88_node3
  · exact profile88_node4

def profile88_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile88_node0 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [] 2 := by
  apply routed_branch (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [] 2 (by decide) (choices 4) [30] profile88_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [] (choices 4) [30] profile88_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile88_node1

theorem profile88 : Upper (D (n:=5) [65,52,51,36,34]) (R (n:=5) [65,52,51,36,34]) [] 2 := profile88_node0

def profile89_node3_cert : CutBound 5 := { lost := (rows 16 0 0 16 0), upper := (rows 15 23 23 15 23), lower := (rows 15 23 23 8 16), losses := [{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile89_node3 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21,19] 2 profile89_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21,19] 2 profile89_node3_cert).mp (by decide +kernel))

def profile89_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node2 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21] 2 (by decide) (choices 3) [19] profile89_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14,21] (choices 3) [19] profile89_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node3

def profile89_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node1 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14] 2 (by decide) (choices 3) [21] profile89_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [14] (choices 3) [21] profile89_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node2

def profile89_node6_cert : CutBound 5 := { lost := (rows 0 16 0 16 0), upper := (rows 23 15 23 15 23), lower := (rows 23 15 23 8 16), losses := [{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile89_node6 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13,19] 2 profile89_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13,19] 2 profile89_node6_cert).mp (by decide +kernel))

def profile89_node5_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node5 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13] 2 (by decide) (choices 3) [19] profile89_node5_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,13] (choices 3) [19] profile89_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node6

def profile89_node7_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node7 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,21] 2 profile89_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,21] 2 profile89_node7_cert).mp (by decide +kernel))

def profile89_node8_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 27 7 15 23), lower := (rows 23 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node8 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,25] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,25] 2 profile89_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22,25] 2 profile89_node8_cert).mp (by decide +kernel))

def profile89_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node4 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22] 2 (by decide) (choices 3) [13,21,25] profile89_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [22] (choices 3) [13,21,25] profile89_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node5
  · exact profile89_node7
  · exact profile89_node8

def profile89_node10_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 27 23 7 15 23), lower := (rows 27 23 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile89_node10 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26,21] 2 profile89_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26,21] 2 profile89_node10_cert).mp (by decide +kernel))

def profile89_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node9 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26] 2 (by decide) (choices 3) [21] profile89_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [26] (choices 3) [21] profile89_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile89_node10

def profile89_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile89_node0 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [] 2 (by decide) (choices 3) [14,22,26] profile89_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [] (choices 3) [14,22,26] profile89_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile89_node1
  · exact profile89_node4
  · exact profile89_node9

theorem profile89 : Upper (D (n:=5) [52,52,51,49,34]) (R (n:=5) [52,52,51,49,34]) [] 2 := profile89_node0

def profile90_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 15 15 23 27 19), lower := (rows 15 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile90_node2 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,13] 2 profile90_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,13] 2 profile90_node2_cert).mp (by decide +kernel))

def profile90_node4_cert : CutBound 5 := { lost := (rows 0 8 0 4 12), upper := (rows 15 23 15 27 19), lower := (rows 15 23 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile90_node4 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,11] 2 profile90_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,11] 2 profile90_node4_cert).mp (by decide +kernel))

def profile90_node5_cert : CutBound 5 := { lost := (rows 0 8 8 4 4), upper := (rows 15 23 23 11 27), lower := (rows 15 23 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) }] }

theorem profile90_node5 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,19] 2 profile90_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21,19] 2 profile90_node5_cert).mp (by decide +kernel))

def profile90_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node3 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21] 2 (by decide) (choices 3) [11,19] profile90_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14,21] (choices 3) [11,19] profile90_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node4
  · exact profile90_node5

def profile90_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile90_node1 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14] 2 (by decide) (choices 3) [13,21] profile90_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [14] (choices 3) [13,21] profile90_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node2
  · exact profile90_node3

def profile90_node8_cert : CutBound 5 := { lost := (rows 8 0 0 4 12), upper := (rows 23 15 15 27 19), lower := (rows 23 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile90_node8 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,11] 2 profile90_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,11] 2 profile90_node8_cert).mp (by decide +kernel))

def profile90_node9_cert : CutBound 5 := { lost := (rows 8 0 8 4 4), upper := (rows 23 15 23 11 27), lower := (rows 23 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) }] }

theorem profile90_node9 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,19] 2 profile90_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13,19] 2 profile90_node9_cert).mp (by decide +kernel))

def profile90_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node7 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13] 2 (by decide) (choices 3) [11,19] profile90_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,13] (choices 3) [11,19] profile90_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node8
  · exact profile90_node9

def profile90_node10_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 23 23 15 11 27), lower := (rows 23 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile90_node10 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,21] 2 profile90_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,21] 2 profile90_node10_cert).mp (by decide +kernel))

def profile90_node12_cert : CutBound 5 := { lost := (rows 8 0 16 16 8), upper := (rows 23 27 15 15 23), lower := (rows 23 27 15 8 16), losses := [{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile90_node12 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25,11] 2 profile90_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25,11] 2 profile90_node12_cert).mp (by decide +kernel))

def profile90_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node11 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25] 2 (by decide) (choices 3) [11] profile90_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22,25] (choices 3) [11] profile90_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile90_node12

def profile90_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile90_node6 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22] 2 (by decide) (choices 3) [13,21,25] profile90_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [22] (choices 3) [13,21,25] profile90_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile90_node7
  · exact profile90_node10
  · exact profile90_node11

def profile90_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile90_node0 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [] 2 (by decide) (choices 3) [14,22] profile90_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [] (choices 3) [14,22] profile90_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile90_node1
  · exact profile90_node6

theorem profile90 : Upper (D (n:=5) [52,52,50,50,34]) (R (n:=5) [52,52,50,50,34]) [] 2 := profile90_node0

def profile91_node2_cert : CutBound 5 := { lost := (rows 16 16 8 0 8), upper := (rows 15 15 23 31 23), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 3 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile91_node2 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,13] 2 profile91_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,13] 2 profile91_node2_cert).mp (by decide +kernel))

def profile91_node4_cert : CutBound 5 := { lost := (rows 16 8 16 0 8), upper := (rows 15 23 15 31 23), lower := (rows 15 23 15 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 5 2 5 8 0), good := (rows 15 7 15 8 0) }] }

theorem profile91_node4 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,11] 2 profile91_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,11] 2 profile91_node4_cert).mp (by decide +kernel))

def profile91_node5_cert : CutBound 5 := { lost := (rows 16 8 8 16 0), upper := (rows 15 23 23 15 31), lower := (rows 15 23 23 8 16), losses := [{ target := 3, region := (rows 1 6 6 0 16), good := (rows 7 23 23 0 16) },{ target := 4, region := (rows 7 2 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile91_node5 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,19] 2 profile91_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,19] 2 profile91_node5_cert).mp (by decide +kernel))

def profile91_node6_cert : CutBound 5 := { lost := (rows 16 8 0 16 8), upper := (rows 15 23 29 15 23), lower := (rows 15 23 29 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile91_node6 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,25] 2 profile91_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21,25] 2 profile91_node6_cert).mp (by decide +kernel))

def profile91_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node3 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21] 2 (by decide) (choices 3) [11,19,25] profile91_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,21] (choices 3) [11,19,25] profile91_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node4
  · exact profile91_node5
  · exact profile91_node6

def profile91_node8_cert : CutBound 5 := { lost := (rows 16 0 8 16 8), upper := (rows 15 27 23 15 23), lower := (rows 15 27 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 5 2 4 13 0), good := (rows 15 11 15 8 0) }] }

theorem profile91_node8 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25,19] 2 profile91_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25,19] 2 profile91_node8_cert).mp (by decide +kernel))

def profile91_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node7 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25] 2 (by decide) (choices 3) [19] profile91_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14,25] (choices 3) [19] profile91_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node8

def profile91_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node1 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14] 2 (by decide) (choices 3) [13,21,25] profile91_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [14] (choices 3) [13,21,25] profile91_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node2
  · exact profile91_node3
  · exact profile91_node7

def profile91_node11_cert : CutBound 5 := { lost := (rows 8 16 16 0 8), upper := (rows 23 15 15 31 23), lower := (rows 23 15 15 8 16), losses := [{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 6 6 8 0), good := (rows 7 15 15 8 0) }] }

theorem profile91_node11 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,11] 2 profile91_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,11] 2 profile91_node11_cert).mp (by decide +kernel))

def profile91_node12_cert : CutBound 5 := { lost := (rows 8 16 8 16 0), upper := (rows 23 15 23 15 31), lower := (rows 23 15 23 8 16), losses := [{ target := 3, region := (rows 5 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile91_node12 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,19] 2 profile91_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,19] 2 profile91_node12_cert).mp (by decide +kernel))

def profile91_node13_cert : CutBound 5 := { lost := (rows 8 16 0 16 8), upper := (rows 23 15 29 15 23), lower := (rows 23 15 29 8 16), losses := [{ target := 3, region := (rows 3 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile91_node13 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,25] 2 profile91_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13,25] 2 profile91_node13_cert).mp (by decide +kernel))

def profile91_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node10 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13] 2 (by decide) (choices 3) [11,19,25] profile91_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,13] (choices 3) [11,19,25] profile91_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node11
  · exact profile91_node12
  · exact profile91_node13

def profile91_node14_cert : CutBound 5 := { lost := (rows 8 8 16 16 0), upper := (rows 23 23 15 15 31), lower := (rows 23 23 4 8 16), losses := [{ target := 3, region := (rows 3 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile91_node14 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,21] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,21] 2 profile91_node14_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,21] 2 profile91_node14_cert).mp (by decide +kernel))

def profile91_node16_cert : CutBound 5 := { lost := (rows 8 0 16 16 8), upper := (rows 23 27 15 15 23), lower := (rows 23 27 15 8 16), losses := [{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile91_node16 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25,11] 2 profile91_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25,11] 2 profile91_node16_cert).mp (by decide +kernel))

def profile91_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node15 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25] 2 (by decide) (choices 3) [11] profile91_node15_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22,25] (choices 3) [11] profile91_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node16

def profile91_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node9 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22] 2 (by decide) (choices 3) [13,21,25] profile91_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [22] (choices 3) [13,21,25] profile91_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node10
  · exact profile91_node14
  · exact profile91_node15

def profile91_node19_cert : CutBound 5 := { lost := (rows 0 16 8 16 8), upper := (rows 27 15 23 15 23), lower := (rows 27 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 6 4 14 0), good := (rows 11 15 15 8 0) }] }

theorem profile91_node19 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13,19] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13,19] 2 profile91_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13,19] 2 profile91_node19_cert).mp (by decide +kernel))

def profile91_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node18 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13] 2 (by decide) (choices 3) [19] profile91_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,13] (choices 3) [19] profile91_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node19

def profile91_node21_cert : CutBound 5 := { lost := (rows 0 8 16 16 8), upper := (rows 27 23 15 15 23), lower := (rows 27 23 15 8 16), losses := [{ target := 3, region := (rows 1 6 4 0 22), good := (rows 19 23 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile91_node21 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21,11] 2 profile91_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21,11] 2 profile91_node21_cert).mp (by decide +kernel))

def profile91_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node20 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21] 2 (by decide) (choices 3) [11] profile91_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26,21] (choices 3) [11] profile91_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile91_node21

def profile91_node17_route : Route 5 := (fun mask => (mask,id))

theorem profile91_node17 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26] 2 (by decide) (choices 3) [13,21] profile91_node17_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [26] (choices 3) [13,21] profile91_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile91_node18
  · exact profile91_node20

def profile91_node0_route : Route 5 := (fun mask => match mask with | 28 => (26,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile91_node0 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [] 2 (by decide) (choices 3) [14,22,26] profile91_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [] (choices 3) [14,22,26] profile91_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile91_node1
  · exact profile91_node9
  · exact profile91_node17

theorem profile91 : Upper (D (n:=5) [52,51,51,50,34]) (R (n:=5) [52,51,51,50,34]) [] 2 := profile91_node0

def profile92_node4_cert : CutBound 5 := { lost := (rows 0 0 8 4 3), upper := (rows 15 15 23 27 28), lower := (rows 15 15 23 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 12 16), good := (rows 11 11 27 27 16) },{ target := 3, region := (rows 1 2 12 0 16), good := (rows 7 7 23 23 16) }] }

theorem profile92_node4 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,19] 2 profile92_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,19] 2 profile92_node4_cert).mp (by decide +kernel))

def profile92_node5_cert : CutBound 5 := { lost := (rows 16 16 0 2 5), upper := (rows 15 15 23 29 26), lower := (rows 15 15 23 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 13 29 29 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 25 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile92_node5 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,21] 2 profile92_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,21] 2 profile92_node5_cert).mp (by decide +kernel))

def profile92_node6_cert : CutBound 5 := { lost := (rows 16 16 0 1 6), upper := (rows 15 15 23 30 25), lower := (rows 15 15 23 30 16), losses := [{ target := 0, region := (rows 0 2 4 12 16), good := (rows 14 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 26 16) },{ target := 4, region := (rows 11 11 4 8 0), good := (rows 15 15 7 15 0) }] }

theorem profile92_node6 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,22] 2 profile92_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19,22] 2 profile92_node6_cert).mp (by decide +kernel))

def profile92_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node3 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19] 2 (by decide) (choices 3) [19,21,22] profile92_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,19] (choices 3) [19,21,22] profile92_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node4
  · exact profile92_node5
  · exact profile92_node6

def profile92_node8_cert : CutBound 5 := { lost := (rows 16 16 2 0 9), upper := (rows 15 15 29 27 22), lower := (rows 15 15 29 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 13 13 29 29 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 19 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 11 0) }] }

theorem profile92_node8 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,19] 2 profile92_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,19] 2 profile92_node8_cert).mp (by decide +kernel))

def profile92_node9_cert : CutBound 5 := { lost := (rows 16 16 0 0 12), upper := (rows 15 15 29 30 19), lower := (rows 15 15 29 30 16), losses := [{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 25 26 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 22 16) },{ target := 4, region := (rows 15 15 4 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node9 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,22] 2 profile92_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25,22] 2 profile92_node9_cert).mp (by decide +kernel))

def profile92_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node7 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25] 2 (by decide) (choices 3) [19,22] profile92_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,25] (choices 3) [19,22] profile92_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node8
  · exact profile92_node9

def profile92_node11_cert : CutBound 5 := { lost := (rows 16 16 1 0 10), upper := (rows 15 15 30 27 21), lower := (rows 15 15 30 27 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 14 14 30 30 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 28 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 19 16) },{ target := 4, region := (rows 7 7 4 8 0), good := (rows 15 15 15 11 0) }] }

theorem profile92_node11 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,19] 2 profile92_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,19] 2 profile92_node11_cert).mp (by decide +kernel))

def profile92_node12_cert : CutBound 5 := { lost := (rows 16 16 0 0 12), upper := (rows 15 15 30 29 19), lower := (rows 15 15 30 29 16), losses := [{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 26 25 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 21 16) },{ target := 4, region := (rows 15 15 4 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node12 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,21] 2 profile92_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26,21] 2 profile92_node12_cert).mp (by decide +kernel))

def profile92_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node10 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26] 2 (by decide) (choices 3) [19,21] profile92_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13,26] (choices 3) [19,21] profile92_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node11
  · exact profile92_node12

def profile92_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node2 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13] 2 (by decide) (choices 3) [19,25,26] profile92_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,13] (choices 3) [19,25,26] profile92_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node3
  · exact profile92_node7
  · exact profile92_node10

def profile92_node15_cert : CutBound 5 := { lost := (rows 16 0 16 4 3), upper := (rows 15 23 15 27 28), lower := (rows 15 23 15 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 25 16) },{ target := 2, region := (rows 1 2 0 10 16), good := (rows 11 27 11 27 16) },{ target := 4, region := (rows 13 2 13 8 0), good := (rows 15 7 15 15 0) }] }

theorem profile92_node15 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,19] 2 profile92_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,19] 2 profile92_node15_cert).mp (by decide +kernel))

def profile92_node16_cert : CutBound 5 := { lost := (rows 0 8 0 2 5), upper := (rows 15 23 15 29 26), lower := (rows 15 23 15 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 10 16), good := (rows 13 29 13 29 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 27 25 16) },{ target := 3, region := (rows 1 10 4 0 16), good := (rows 7 23 7 23 16) }] }

theorem profile92_node16 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,21] 2 profile92_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,21] 2 profile92_node16_cert).mp (by decide +kernel))

def profile92_node17_cert : CutBound 5 := { lost := (rows 16 0 16 1 6), upper := (rows 15 23 15 30 25), lower := (rows 15 23 15 30 16), losses := [{ target := 0, region := (rows 0 2 4 10 16), good := (rows 14 30 14 30 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 27 26 16) },{ target := 4, region := (rows 13 2 13 8 0), good := (rows 15 7 15 15 0) }] }

theorem profile92_node17 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,22] 2 profile92_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11,22] 2 profile92_node17_cert).mp (by decide +kernel))

def profile92_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node14 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11] 2 (by decide) (choices 3) [19,21,22] profile92_node14_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,11] (choices 3) [19,21,22] profile92_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node15
  · exact profile92_node16
  · exact profile92_node17

def profile92_node19_cert : CutBound 5 := { lost := (rows 16 8 0 16 5), upper := (rows 15 23 29 15 26), lower := (rows 15 23 29 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 25), good := (rows 30 22 28 30 16) },{ target := 2, region := (rows 1 2 0 8 25), good := (rows 27 19 25 27 16) },{ target := 3, region := (rows 1 6 4 0 16), good := (rows 7 23 23 7 16) },{ target := 4, region := (rows 11 2 4 11 0), good := (rows 15 15 13 15 0) }] }

theorem profile92_node19 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25,7] 2 profile92_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25,7] 2 profile92_node19_cert).mp (by decide +kernel))

def profile92_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node18 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25] 2 (by decide) (choices 3) [7] profile92_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,25] (choices 3) [7] profile92_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node19

def profile92_node21_cert : CutBound 5 := { lost := (rows 16 0 0 16 6), upper := (rows 15 23 30 15 25), lower := (rows 15 23 30 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 25), good := (rows 29 21 28 29 16) },{ target := 2, region := (rows 1 2 0 8 25), good := (rows 27 19 26 27 16) },{ target := 4, region := (rows 15 2 4 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node21 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26,7] 2 profile92_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26,7] 2 profile92_node21_cert).mp (by decide +kernel))

def profile92_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node20 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26] 2 (by decide) (choices 3) [7] profile92_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21,26] (choices 3) [7] profile92_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node21

def profile92_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node13 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21] 2 (by decide) (choices 3) [11,25,26] profile92_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,21] (choices 3) [11,25,26] profile92_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node14
  · exact profile92_node18
  · exact profile92_node20

def profile92_node24_cert : CutBound 5 := { lost := (rows 16 0 16 0 10), upper := (rows 15 30 15 27 21), lower := (rows 15 30 15 27 16), losses := [{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 28 29 25 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 19 16) },{ target := 4, region := (rows 15 2 15 8 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node24 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,19] 2 profile92_node24_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,19] 2 profile92_node24_cert).mp (by decide +kernel))

def profile92_node25_cert : CutBound 5 := { lost := (rows 16 1 16 0 12), upper := (rows 15 30 15 29 19), lower := (rows 15 30 15 29 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 14 30 14 30 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 26 27 25 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 21 16) },{ target := 4, region := (rows 7 2 7 8 0), good := (rows 15 15 15 13 0) }] }

theorem profile92_node25 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,21] 2 profile92_node25_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11,21] 2 profile92_node25_cert).mp (by decide +kernel))

def profile92_node23_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node23 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11] 2 (by decide) (choices 3) [19,21] profile92_node23_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,11] (choices 3) [19,21] profile92_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node24
  · exact profile92_node25

def profile92_node27_cert : CutBound 5 := { lost := (rows 16 0 0 16 6), upper := (rows 15 30 23 15 25), lower := (rows 15 30 23 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 25), good := (rows 29 28 21 29 16) },{ target := 2, region := (rows 1 2 0 8 25), good := (rows 27 26 19 27 16) },{ target := 4, region := (rows 15 2 4 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node27 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19,7] 2 profile92_node27_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19,7] 2 profile92_node27_cert).mp (by decide +kernel))

def profile92_node26_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node26 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19] 2 (by decide) (choices 3) [7] profile92_node26_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,19] (choices 3) [7] profile92_node26_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node27

def profile92_node28_cert : CutBound 5 := { lost := (rows 16 1 0 16 8), upper := (rows 15 30 29 15 23), lower := (rows 15 30 29 8 16), losses := [{ target := 0, region := (rows 0 6 4 8 16), good := (rows 14 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 22 21 0 16) },{ target := 4, region := (rows 3 2 4 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile92_node28 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,25] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,25] 2 profile92_node28_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28,25] 2 profile92_node28_cert).mp (by decide +kernel))

def profile92_node22_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node22 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28] 2 (by decide) (choices 3) [11,19,25] profile92_node22_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14,28] (choices 3) [11,19,25] profile92_node22_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node23
  · exact profile92_node26
  · exact profile92_node28

def profile92_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile92_node1 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14] 2 (by decide) (choices 3) [13,21,28] profile92_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [14] (choices 3) [13,21,28] profile92_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node2
  · exact profile92_node13
  · exact profile92_node22

def profile92_node32_cert : CutBound 5 := { lost := (rows 0 16 16 4 3), upper := (rows 23 15 15 27 28), lower := (rows 23 15 15 27 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 30 26 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 29 29 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 27 16) },{ target := 4, region := (rows 1 14 14 8 0), good := (rows 7 15 15 15 0) }] }

theorem profile92_node32 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,19] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,19] 2 profile92_node32_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,19] 2 profile92_node32_cert).mp (by decide +kernel))

def profile92_node33_cert : CutBound 5 := { lost := (rows 0 16 16 2 5), upper := (rows 23 15 15 29 26), lower := (rows 23 15 15 29 16), losses := [{ target := 0, region := (rows 0 2 4 8 22), good := (rows 22 30 30 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 29 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 19 27 27 25 16) },{ target := 4, region := (rows 1 14 14 8 0), good := (rows 7 15 15 15 0) }] }

theorem profile92_node33 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,21] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,21] 2 profile92_node33_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,21] 2 profile92_node33_cert).mp (by decide +kernel))

def profile92_node34_cert : CutBound 5 := { lost := (rows 8 0 0 1 6), upper := (rows 23 15 15 30 25), lower := (rows 23 15 15 30 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 30 16) },{ target := 1, region := (rows 1 0 4 8 22), good := (rows 21 29 29 28 16) },{ target := 2, region := (rows 1 2 0 8 22), good := (rows 19 27 27 26 16) },{ target := 3, region := (rows 9 2 4 0 16), good := (rows 23 7 7 23 16) }] }

theorem profile92_node34 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,22] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,22] 2 profile92_node34_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11,22] 2 profile92_node34_cert).mp (by decide +kernel))

def profile92_node31_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node31 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11] 2 (by decide) (choices 3) [19,21,22] profile92_node31_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,11] (choices 3) [19,21,22] profile92_node31_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node32
  · exact profile92_node33
  · exact profile92_node34

def profile92_node36_cert : CutBound 5 := { lost := (rows 0 16 0 16 5), upper := (rows 23 15 29 15 26), lower := (rows 23 15 29 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 26), good := (rows 22 30 28 30 16) },{ target := 2, region := (rows 1 2 0 8 26), good := (rows 19 27 25 27 16) },{ target := 4, region := (rows 1 15 4 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node36 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25,7] 2 profile92_node36_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25,7] 2 profile92_node36_cert).mp (by decide +kernel))

def profile92_node35_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node35 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25] 2 (by decide) (choices 3) [7] profile92_node35_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,25] (choices 3) [7] profile92_node35_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node36

def profile92_node38_cert : CutBound 5 := { lost := (rows 8 16 0 16 6), upper := (rows 23 15 30 15 25), lower := (rows 23 15 30 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 26), good := (rows 21 29 28 29 16) },{ target := 2, region := (rows 1 2 0 8 26), good := (rows 19 27 26 27 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 23 7 23 7 16) },{ target := 4, region := (rows 1 11 4 11 0), good := (rows 15 15 14 15 0) }] }

theorem profile92_node38 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26,7] 2 profile92_node38_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26,7] 2 profile92_node38_cert).mp (by decide +kernel))

def profile92_node37_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node37 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26] 2 (by decide) (choices 3) [7] profile92_node37_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13,26] (choices 3) [7] profile92_node37_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node38

def profile92_node30_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node30 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13] 2 (by decide) (choices 3) [11,25,26] profile92_node30_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,13] (choices 3) [11,25,26] profile92_node30_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node31
  · exact profile92_node35
  · exact profile92_node37

def profile92_node41_cert : CutBound 5 := { lost := (rows 0 0 16 16 3), upper := (rows 23 27 15 15 28), lower := (rows 23 27 15 15 16), losses := [{ target := 0, region := (rows 0 2 4 8 28), good := (rows 22 26 30 30 16) },{ target := 1, region := (rows 1 0 4 8 28), good := (rows 21 25 29 29 16) },{ target := 4, region := (rows 1 2 15 15 0), good := (rows 15 15 15 15 0) }] }

theorem profile92_node41 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11,7] 2 profile92_node41_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11,7] 2 profile92_node41_cert).mp (by decide +kernel))

def profile92_node40_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node40 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11] 2 (by decide) (choices 3) [7] profile92_node40_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25,11] (choices 3) [7] profile92_node40_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node41

def profile92_node39_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node39 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25] 2 (by decide) (choices 3) [11] profile92_node39_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,25] (choices 3) [11] profile92_node39_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node40

def profile92_node44_cert : CutBound 5 := { lost := (rows 8 0 16 16 6), upper := (rows 23 30 15 15 25), lower := (rows 23 30 15 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 28), good := (rows 21 28 29 29 16) },{ target := 2, region := (rows 1 2 0 8 28), good := (rows 19 26 27 27 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 23 23 7 7 16) },{ target := 4, region := (rows 1 2 13 13 0), good := (rows 15 14 15 15 0) }] }

theorem profile92_node44 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11,7] 2 :=
  cut_bound_sound (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11,7] 2 profile92_node44_cert
    ((SmallCut.boundCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11,7] 2 profile92_node44_cert).mp (by decide +kernel))

def profile92_node43_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node43 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11] 2 (by decide) (choices 3) [7] profile92_node43_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28,11] (choices 3) [7] profile92_node43_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node44

def profile92_node42_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node42 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28] 2 (by decide) (choices 3) [11] profile92_node42_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22,28] (choices 3) [11] profile92_node42_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile92_node43

def profile92_node29_route : Route 5 := (fun mask => (mask,id))

theorem profile92_node29 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22] 2 (by decide) (choices 3) [13,25,28] profile92_node29_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [22] (choices 3) [13,25,28] profile92_node29_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile92_node30
  · exact profile92_node39
  · exact profile92_node42

def profile92_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile92_node0 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [] 2 := by
  apply routed_branch (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [] 2 (by decide) (choices 3) [14,22] profile92_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [] (choices 3) [14,22] profile92_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile92_node1
  · exact profile92_node29

theorem profile92 : Upper (D (n:=5) [51,51,51,51,34]) (R (n:=5) [51,51,51,51,34]) [] 2 := profile92_node0

def profile93_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 31 13 29 21), lower := (rows 31 31 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 0 16) }] }

theorem profile93_node3 : Upper (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29,9] 2 profile93_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29,9] 2 profile93_node3_cert).mp (by decide +kernel))

def profile93_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile93_node2 : Upper (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29] 2 (by decide) (choices 2) [9] profile93_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30,29] (choices 2) [9] profile93_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node3

def profile93_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node1 : Upper (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30] 2 (by decide) (choices 4) [29] profile93_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [30] (choices 4) [29] profile93_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node2

def profile93_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile93_node0 : Upper (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [] 2 (by decide) (choices 4) [30] profile93_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [] (choices 4) [30] profile93_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile93_node1

theorem profile93 : Upper (D (n:=5) [68,65,35,35,35]) (R (n:=5) [68,65,35,35,35]) [] 2 := profile93_node0

def profile94_node3_cert : CutBound 5 := { lost := (rows 0 0 24 2 2), upper := (rows 31 31 7 29 29), lower := (rows 31 31 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 8 0), good := (rows 15 15 7 8 0) }] }

theorem profile94_node3 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,3] 2 profile94_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,3] 2 profile94_node3_cert).mp (by decide +kernel))

def profile94_node5_cert : CutBound 5 := { lost := (rows 0 0 2 6 1), upper := (rows 31 31 13 25 22), lower := (rows 31 31 13 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 28 24 16) },{ target := 1, region := (rows 1 0 15 11 16), good := (rows 29 29 13 29 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 27 9 25 16) }] }

theorem profile94_node5 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,17] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,17] 2 profile94_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,17] 2 profile94_node5_cert).mp (by decide +kernel))

def profile94_node6_cert : CutBound 5 := { lost := (rows 0 0 2 5 2), upper := (rows 31 31 13 26 21), lower := (rows 31 31 13 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 30 12 26 16) },{ target := 1, region := (rows 1 0 7 8 23), good := (rows 29 29 29 28 16) },{ target := 2, region := (rows 1 2 0 11 16), good := (rows 27 27 9 26 16) }] }

theorem profile94_node6 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,18] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,18] 2 profile94_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,18] 2 profile94_node6_cert).mp (by decide +kernel))

def profile94_node7_cert : CutBound 5 := { lost := (rows 0 0 2 3 4), upper := (rows 31 31 13 28 19), lower := (rows 31 31 13 28 16), losses := [{ target := 0, region := (rows 0 2 4 11 16), good := (rows 30 30 12 28 16) },{ target := 1, region := (rows 1 0 7 11 16), good := (rows 29 29 13 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 25 24 16) }] }

theorem profile94_node7 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,20] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,20] 2 profile94_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9,20] 2 profile94_node7_cert).mp (by decide +kernel))

def profile94_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node4 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9] 2 (by decide) (choices 2) [17,18,20] profile94_node4_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,9] (choices 2) [17,18,20] profile94_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile94_node5
  · exact profile94_node6
  · exact profile94_node7

def profile94_node8_cert : CutBound 5 := { lost := (rows 0 0 1 2 10), upper := (rows 31 31 14 29 21), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile94_node8 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,10] 2 profile94_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,10] 2 profile94_node8_cert).mp (by decide +kernel))

def profile94_node9_cert : CutBound 5 := { lost := (rows 0 0 3 16 8), upper := (rows 31 31 28 15 23), lower := (rows 31 31 28 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 28 8 16) },{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 20 0 16) },{ target := 4, region := (rows 1 2 4 11 0), good := (rows 15 15 12 8 0) }] }

theorem profile94_node9 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,24] 2 :=
  cut_bound_sound (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,24] 2 profile94_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29,24] 2 profile94_node9_cert).mp (by decide +kernel))

def profile94_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile94_node2 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29] 2 (by decide) (choices 2) [3,9,10,24] profile94_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30,29] (choices 2) [3,9,10,24] profile94_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile94_node3
  · exact profile94_node4
  · exact profile94_node8
  · exact profile94_node9

def profile94_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node1 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30] 2 (by decide) (choices 4) [29] profile94_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [30] (choices 4) [29] profile94_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node2

def profile94_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile94_node0 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [] 2 (by decide) (choices 4) [30] profile94_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [] (choices 4) [30] profile94_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile94_node1

theorem profile94 : Upper (D (n:=5) [67,66,35,35,35]) (R (n:=5) [67,66,35,35,35]) [] 2 := profile94_node0

def profile95_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 31 13 29 21), lower := (rows 31 31 13 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 21 0 16) }] }

theorem profile95_node3 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,9] 2 profile95_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,9] 2 profile95_node3_cert).mp (by decide +kernel))

def profile95_node4_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 28 13 21), lower := (rows 31 31 28 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 28 8 16) }] }

theorem profile95_node4 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,24] 2 :=
  cut_bound_sound (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,24] 2 profile95_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29,24] 2 profile95_node4_cert).mp (by decide +kernel))

def profile95_node2_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile95_node2 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29] 2 (by decide) (choices 2) [9,24] profile95_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30,29] (choices 2) [9,24] profile95_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile95_node3
  · exact profile95_node4

def profile95_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node1 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30] 2 (by decide) (choices 4) [29] profile95_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [30] (choices 4) [29] profile95_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile95_node2

def profile95_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile95_node0 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [] 2 := by
  apply routed_branch (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [] 2 (by decide) (choices 4) [30] profile95_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [] (choices 4) [30] profile95_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile95_node1

theorem profile95 : Upper (D (n:=5) [67,65,36,35,35]) (R (n:=5) [67,65,36,35,35]) [] 2 := profile95_node0

#print axioms profile95
end Delivery.FiveVertexPositive14
