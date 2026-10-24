import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile47_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile47_node2 : Upper (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30,13] 2 profile47_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30,13] 2 profile47_node2_cert).mp (by decide +kernel))

def profile47_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node1 : Upper (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30] 2 (by decide) (choices 3) [13] profile47_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [30] (choices 3) [13] profile47_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node2

def profile47_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile47_node0 : Upper (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [] 2 (by decide) (choices 4) [30] profile47_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [] (choices 4) [30] profile47_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node1

theorem profile47 : Upper (D (n:=5) [67,52,52,34,33]) (R (n:=5) [67,52,52,34,33]) [] 2 := profile47_node0

def profile48_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node1 : Upper (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [30] 2 (by decide) (choices 4) [] profile48_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [30] (choices 4) [] profile48_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile48_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile48_node0 : Upper (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [] 2 (by decide) (choices 4) [30] profile48_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [] (choices 4) [30] profile48_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node1

theorem profile48 : Upper (D (n:=5) [68,67,35,35,33]) (R (n:=5) [68,67,35,35,33]) [] 2 := profile48_node0

def profile49_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node1 : Upper (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [30] 2 (by decide) (choices 4) [] profile49_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [30] (choices 4) [] profile49_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile49_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile49_node0 : Upper (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [] 2 (by decide) (choices 4) [30] profile49_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [] (choices 4) [30] profile49_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node1

theorem profile49 : Upper (D (n:=5) [68,66,36,35,33]) (R (n:=5) [68,66,36,35,33]) [] 2 := profile49_node0

def profile50_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node1 : Upper (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [30] 2 (by decide) (choices 4) [] profile50_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [30] (choices 4) [] profile50_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile50_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile50_node0 : Upper (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [] 2 (by decide) (choices 4) [30] profile50_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [] (choices 4) [30] profile50_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node1

theorem profile50 : Upper (D (n:=5) [67,67,36,35,33]) (R (n:=5) [67,67,36,35,33]) [] 2 := profile50_node0

def profile51_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 15 15 11 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile51_node2 : Upper (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30,13] 2 profile51_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30,13] 2 profile51_node2_cert).mp (by decide +kernel))

def profile51_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node1 : Upper (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30] 2 (by decide) (choices 3) [13] profile51_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [30] (choices 3) [13] profile51_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node2

def profile51_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile51_node0 : Upper (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [] 2 (by decide) (choices 4) [30] profile51_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [] (choices 4) [30] profile51_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node1

theorem profile51 : Upper (D (n:=5) [68,52,50,35,33]) (R (n:=5) [68,52,50,35,33]) [] 2 := profile51_node0

def profile52_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 15 15 15 23), lower := (rows 31 15 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile52_node3 : Upper (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13,11] 2 profile52_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13,11] 2 profile52_node3_cert).mp (by decide +kernel))

def profile52_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node2 : Upper (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13] 2 (by decide) (choices 3) [11] profile52_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30,13] (choices 3) [11] profile52_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node3

def profile52_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node1 : Upper (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30] 2 (by decide) (choices 3) [13] profile52_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [30] (choices 3) [13] profile52_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node2

def profile52_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile52_node0 : Upper (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [] 2 (by decide) (choices 4) [30] profile52_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [] (choices 4) [30] profile52_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile52_node1

theorem profile52 : Upper (D (n:=5) [68,51,51,35,33]) (R (n:=5) [68,51,51,35,33]) [] 2 := profile52_node0

def profile53_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 31 15 15 15 23), lower := (rows 31 15 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile53_node3 : Upper (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13,11] 2 profile53_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13,11] 2 profile53_node3_cert).mp (by decide +kernel))

def profile53_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node2 : Upper (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13] 2 (by decide) (choices 3) [11] profile53_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30,13] (choices 3) [11] profile53_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node3

def profile53_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node1 : Upper (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30] 2 (by decide) (choices 3) [13] profile53_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [30] (choices 3) [13] profile53_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node2

def profile53_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile53_node0 : Upper (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [] 2 (by decide) (choices 4) [30] profile53_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [] (choices 4) [30] profile53_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile53_node1

theorem profile53 : Upper (D (n:=5) [67,52,51,35,33]) (R (n:=5) [67,52,51,35,33]) [] 2 := profile53_node0

def profile54_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 15 14 22), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile54_node3 : Upper (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13,11] 2 profile54_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13,11] 2 profile54_node3_cert).mp (by decide +kernel))

def profile54_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node2 : Upper (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13] 2 (by decide) (choices 3) [11] profile54_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30,13] (choices 3) [11] profile54_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node3

def profile54_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node1 : Upper (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30] 2 (by decide) (choices 3) [13] profile54_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [30] (choices 3) [13] profile54_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node2

def profile54_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile54_node0 : Upper (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [] 2 (by decide) (choices 4) [30] profile54_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [] (choices 4) [30] profile54_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile54_node1

theorem profile54 : Upper (D (n:=5) [66,52,52,35,33]) (R (n:=5) [66,52,52,35,33]) [] 2 := profile54_node0

def profile55_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node1 : Upper (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [30] 2 (by decide) (choices 4) [] profile55_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [30] (choices 4) [] profile55_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile55_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile55_node0 : Upper (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [] 2 (by decide) (choices 4) [30] profile55_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [] (choices 4) [30] profile55_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile55_node1

theorem profile55 : Upper (D (n:=5) [67,66,36,36,33]) (R (n:=5) [67,66,36,36,33]) [] 2 := profile55_node0

def profile56_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 15 15 11 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile56_node2 : Upper (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30,13] 2 profile56_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30,13] 2 profile56_node2_cert).mp (by decide +kernel))

def profile56_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node1 : Upper (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30] 2 (by decide) (choices 3) [13] profile56_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [30] (choices 3) [13] profile56_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node2

def profile56_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile56_node0 : Upper (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [] 2 (by decide) (choices 4) [30] profile56_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [] (choices 4) [30] profile56_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile56_node1

theorem profile56 : Upper (D (n:=5) [68,51,50,36,33]) (R (n:=5) [68,51,50,36,33]) [] 2 := profile56_node0

def profile57_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 4), upper := (rows 31 15 15 11 27), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile57_node2 : Upper (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30,13] 2 profile57_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30,13] 2 profile57_node2_cert).mp (by decide +kernel))

def profile57_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node1 : Upper (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30] 2 (by decide) (choices 3) [13] profile57_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [30] (choices 3) [13] profile57_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node2

def profile57_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile57_node0 : Upper (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [] 2 (by decide) (choices 4) [30] profile57_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [] (choices 4) [30] profile57_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile57_node1

theorem profile57 : Upper (D (n:=5) [67,52,50,36,33]) (R (n:=5) [67,52,50,36,33]) [] 2 := profile57_node0

def profile58_node4_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 31 15 15 11 28), lower := (rows 31 15 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 30 26 16) }] }

theorem profile58_node4 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,3] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,3] 2 profile58_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,3] 2 profile58_node4_cert).mp (by decide +kernel))

def profile58_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 1), upper := (rows 31 15 15 13 26), lower := (rows 31 15 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 30 28 16) }] }

theorem profile58_node5 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,5] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,5] 2 profile58_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,5] 2 profile58_node5_cert).mp (by decide +kernel))

def profile58_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 15 15 14 25), lower := (rows 31 15 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 14 14 16) }] }

theorem profile58_node6 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,6] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,6] 2 profile58_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11,6] 2 profile58_node6_cert).mp (by decide +kernel))

def profile58_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node3 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11] 2 (by decide) (choices 2) [3,5,6] profile58_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13,11] (choices 2) [3,5,6] profile58_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile58_node4
  · exact profile58_node5
  · exact profile58_node6

def profile58_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node2 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13] 2 (by decide) (choices 3) [11] profile58_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30,13] (choices 3) [11] profile58_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node3

def profile58_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node1 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30] 2 (by decide) (choices 3) [13] profile58_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [30] (choices 3) [13] profile58_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node2

def profile58_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile58_node0 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [] 2 (by decide) (choices 4) [30] profile58_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [] (choices 4) [30] profile58_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile58_node1

theorem profile58 : Upper (D (n:=5) [67,51,51,36,33]) (R (n:=5) [67,51,51,36,33]) [] 2 := profile58_node0

def profile59_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 1), upper := (rows 31 15 15 14 30), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile59_node3 : Upper (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13,11] 2 profile59_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13,11] 2 profile59_node3_cert).mp (by decide +kernel))

def profile59_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node2 : Upper (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13] 2 (by decide) (choices 3) [11] profile59_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30,13] (choices 3) [11] profile59_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node3

def profile59_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node1 : Upper (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30] 2 (by decide) (choices 3) [13] profile59_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [30] (choices 3) [13] profile59_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node2

def profile59_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile59_node0 : Upper (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [] 2 (by decide) (choices 4) [30] profile59_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [] (choices 4) [30] profile59_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile59_node1

theorem profile59 : Upper (D (n:=5) [66,52,51,36,33]) (R (n:=5) [66,52,51,36,33]) [] 2 := profile59_node0

def profile60_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 15 23 31 23), lower := (rows 15 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile60_node2 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,13] 2 profile60_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,13] 2 profile60_node2_cert).mp (by decide +kernel))

def profile60_node4_cert : CutBound 5 := { lost := (rows 0 8 0 0 8), upper := (rows 15 23 15 15 23), lower := (rows 15 23 15 8 16), losses := [{ target := 3, region := (rows 1 7 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile60_node4 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21,11] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21,11] 2 profile60_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21,11] 2 profile60_node4_cert).mp (by decide +kernel))

def profile60_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node3 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21] 2 (by decide) (choices 3) [11] profile60_node3_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,21] (choices 3) [11] profile60_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node4

def profile60_node5_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 15 27 7 15 23), lower := (rows 15 27 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile60_node5 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,25] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,25] 2 profile60_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14,25] 2 profile60_node5_cert).mp (by decide +kernel))

def profile60_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node1 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14] 2 (by decide) (choices 3) [13,21,25] profile60_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [14] (choices 3) [13,21,25] profile60_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile60_node2
  · exact profile60_node3
  · exact profile60_node5

def profile60_node8_cert : CutBound 5 := { lost := (rows 8 0 0 0 8), upper := (rows 23 15 15 15 23), lower := (rows 23 15 15 8 16), losses := [{ target := 3, region := (rows 7 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile60_node8 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13,11] 2 profile60_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13,11] 2 profile60_node8_cert).mp (by decide +kernel))

def profile60_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node7 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13] 2 (by decide) (choices 3) [11] profile60_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22,13] (choices 3) [11] profile60_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node8

def profile60_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node6 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22] 2 (by decide) (choices 3) [13] profile60_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [22] (choices 3) [13] profile60_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node7

def profile60_node10_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 27 15 7 15 23), lower := (rows 27 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile60_node10 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26,13] 2 :=
  cut_bound_sound (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26,13] 2 profile60_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26,13] 2 profile60_node10_cert).mp (by decide +kernel))

def profile60_node9_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node9 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26] 2 (by decide) (choices 3) [13] profile60_node9_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [26] (choices 3) [13] profile60_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile60_node10

def profile60_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile60_node0 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [] 2 (by decide) (choices 3) [14,22,26] profile60_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [] (choices 3) [14,22,26] profile60_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile60_node1
  · exact profile60_node6
  · exact profile60_node9

theorem profile60 : Upper (D (n:=5) [52,52,51,50,33]) (R (n:=5) [52,52,51,50,33]) [] 2 := profile60_node0

def profile61_node3_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 15 15 15 31 23), lower := (rows 15 15 15 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile61_node3 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,11] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,11] 2 profile61_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,11] 2 profile61_node3_cert).mp (by decide +kernel))

def profile61_node5_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 15 15 23 15 25), lower := (rows 15 15 23 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 27), good := (rows 29 29 21 29 16) }] }

theorem profile61_node5 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19,7] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19,7] 2 profile61_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19,7] 2 profile61_node5_cert).mp (by decide +kernel))

def profile61_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node4 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19] 2 (by decide) (choices 3) [7] profile61_node4_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,19] (choices 3) [7] profile61_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node5

def profile61_node6_cert : CutBound 5 := { lost := (rows 0 0 0 0 8), upper := (rows 15 15 29 15 23), lower := (rows 15 15 29 8 16), losses := [{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile61_node6 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,25] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,25] 2 profile61_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13,25] 2 profile61_node6_cert).mp (by decide +kernel))

def profile61_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node2 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13] 2 (by decide) (choices 3) [11,19,25] profile61_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,13] (choices 3) [11,19,25] profile61_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile61_node3
  · exact profile61_node4
  · exact profile61_node6

def profile61_node9_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 15 23 15 15 25), lower := (rows 15 23 15 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 29), good := (rows 29 21 29 29 16) }] }

theorem profile61_node9 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11,7] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11,7] 2 profile61_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11,7] 2 profile61_node9_cert).mp (by decide +kernel))

def profile61_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node8 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11] 2 (by decide) (choices 3) [7] profile61_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21,11] (choices 3) [7] profile61_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node9

def profile61_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node7 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21] 2 (by decide) (choices 3) [11] profile61_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14,21] (choices 3) [11] profile61_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node8

def profile61_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile61_node1 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14] 2 (by decide) (choices 3) [13,21] profile61_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [14] (choices 3) [13,21] profile61_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile61_node2
  · exact profile61_node7

def profile61_node13_cert : CutBound 5 := { lost := (rows 0 0 0 0 2), upper := (rows 23 15 15 15 25), lower := (rows 23 15 15 15 16), losses := [{ target := 1, region := (rows 1 0 4 8 30), good := (rows 21 29 29 29 16) }] }

theorem profile61_node13 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11,7] 2 :=
  cut_bound_sound (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11,7] 2 profile61_node13_cert
    ((SmallCut.boundCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11,7] 2 profile61_node13_cert).mp (by decide +kernel))

def profile61_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node12 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11] 2 (by decide) (choices 3) [7] profile61_node12_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13,11] (choices 3) [7] profile61_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node13

def profile61_node11_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node11 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13] 2 (by decide) (choices 3) [11] profile61_node11_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22,13] (choices 3) [11] profile61_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node12

def profile61_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile61_node10 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22] 2 (by decide) (choices 3) [13] profile61_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [22] (choices 3) [13] profile61_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile61_node11

def profile61_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile61_node0 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [] 2 := by
  apply routed_branch (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [] 2 (by decide) (choices 3) [14,22] profile61_node0_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [] (choices 3) [14,22] profile61_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile61_node1
  · exact profile61_node10

theorem profile61 : Upper (D (n:=5) [52,51,51,51,33]) (R (n:=5) [52,51,51,51,33]) [] 2 := profile61_node0

def profile62_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 31 31 7 11 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile62_node2 : Upper (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30,29] 2 profile62_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30,29] 2 profile62_node2_cert).mp (by decide +kernel))

def profile62_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node1 : Upper (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30] 2 (by decide) (choices 4) [29] profile62_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [30] (choices 4) [29] profile62_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node2

def profile62_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile62_node0 : Upper (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [] 2 (by decide) (choices 4) [30] profile62_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [] (choices 4) [30] profile62_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile62_node1

theorem profile62 : Upper (D (n:=5) [68,68,34,34,34]) (R (n:=5) [68,68,34,34,34]) [] 2 := profile62_node0

def profile63_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 8), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile63_node2 : Upper (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30,29] 2 profile63_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30,29] 2 profile63_node2_cert).mp (by decide +kernel))

def profile63_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node1 : Upper (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30] 2 (by decide) (choices 4) [29] profile63_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [30] (choices 4) [29] profile63_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile63_node2

def profile63_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile63_node0 : Upper (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [] 2 (by decide) (choices 4) [30] profile63_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [] (choices 4) [30] profile63_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile63_node1

theorem profile63 : Upper (D (n:=5) [68,67,35,34,34]) (R (n:=5) [68,67,35,34,34]) [] 2 := profile63_node0

def profile64_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 8), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile64_node2 : Upper (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30,29] 2 profile64_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30,29] 2 profile64_node2_cert).mp (by decide +kernel))

def profile64_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile64_node1 : Upper (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30] 2 (by decide) (choices 4) [29] profile64_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [30] (choices 4) [29] profile64_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile64_node2

def profile64_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile64_node0 : Upper (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [] 2 (by decide) (choices 4) [30] profile64_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [] (choices 4) [30] profile64_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile64_node1

theorem profile64 : Upper (D (n:=5) [68,66,36,34,34]) (R (n:=5) [68,66,36,34,34]) [] 2 := profile64_node0

def profile65_node2_cert : CutBound 5 := { lost := (rows 0 0 24 16 8), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile65_node2 : Upper (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30,29] 2 profile65_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30,29] 2 profile65_node2_cert).mp (by decide +kernel))

def profile65_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile65_node1 : Upper (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30] 2 (by decide) (choices 4) [29] profile65_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [30] (choices 4) [29] profile65_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile65_node2

def profile65_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile65_node0 : Upper (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [] 2 (by decide) (choices 4) [30] profile65_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [] (choices 4) [30] profile65_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile65_node1

theorem profile65 : Upper (D (n:=5) [67,67,36,34,34]) (R (n:=5) [67,67,36,34,34]) [] 2 := profile65_node0

def profile66_node2_cert : CutBound 5 := { lost := (rows 0 0 8 4 12), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile66_node2 : Upper (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,13] 2 profile66_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,13] 2 profile66_node2_cert).mp (by decide +kernel))

def profile66_node3_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile66_node3 : Upper (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,25] 2 profile66_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30,25] 2 profile66_node3_cert).mp (by decide +kernel))

def profile66_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile66_node1 : Upper (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30] 2 (by decide) (choices 3) [13,25] profile66_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [30] (choices 3) [13,25] profile66_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile66_node2
  · exact profile66_node3

def profile66_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile66_node0 : Upper (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [] 2 (by decide) (choices 4) [30] profile66_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [] (choices 4) [30] profile66_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile66_node1

theorem profile66 : Upper (D (n:=5) [68,52,50,34,34]) (R (n:=5) [68,52,50,34,34]) [] 2 := profile66_node0

def profile67_node3_cert : CutBound 5 := { lost := (rows 0 16 8 16 8), upper := (rows 31 15 23 15 23), lower := (rows 31 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile67_node3 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13,19] 2 profile67_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13,19] 2 profile67_node3_cert).mp (by decide +kernel))

def profile67_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node2 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13] 2 (by decide) (choices 3) [19] profile67_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,13] (choices 3) [19] profile67_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node3

def profile67_node4_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile67_node4 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,25] 2 profile67_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30,25] 2 profile67_node4_cert).mp (by decide +kernel))

def profile67_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile67_node1 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30] 2 (by decide) (choices 3) [13,25] profile67_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [30] (choices 3) [13,25] profile67_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile67_node2
  · exact profile67_node4

def profile67_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile67_node0 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [] 2 (by decide) (choices 4) [30] profile67_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [] (choices 4) [30] profile67_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile67_node1

theorem profile67 : Upper (D (n:=5) [68,51,51,34,34]) (R (n:=5) [68,51,51,34,34]) [] 2 := profile67_node0

def profile68_node3_cert : CutBound 5 := { lost := (rows 0 16 8 16 8), upper := (rows 31 15 23 15 23), lower := (rows 31 15 23 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile68_node3 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13,19] 2 profile68_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13,19] 2 profile68_node3_cert).mp (by decide +kernel))

def profile68_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node2 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13] 2 (by decide) (choices 3) [19] profile68_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,13] (choices 3) [19] profile68_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node3

def profile68_node4_cert : CutBound 5 := { lost := (rows 0 4 24 16 8), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile68_node4 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,25] 2 profile68_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,25] 2 profile68_node4_cert).mp (by decide +kernel))

def profile68_node5_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile68_node5 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,28] 2 profile68_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30,28] 2 profile68_node5_cert).mp (by decide +kernel))

def profile68_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile68_node1 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30] 2 (by decide) (choices 3) [13,25,28] profile68_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [30] (choices 3) [13,25,28] profile68_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile68_node2
  · exact profile68_node4
  · exact profile68_node5

def profile68_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile68_node0 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [] 2 (by decide) (choices 4) [30] profile68_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [] (choices 4) [30] profile68_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile68_node1

theorem profile68 : Upper (D (n:=5) [67,52,51,34,34]) (R (n:=5) [67,52,51,34,34]) [] 2 := profile68_node0

def profile69_node3_cert : CutBound 5 := { lost := (rows 0 0 8 1 9), upper := (rows 31 15 23 14 22), lower := (rows 31 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 7 0 23), good := (rows 23 23 23 0 16) }] }

theorem profile69_node3 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13,19] 2 profile69_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13,19] 2 profile69_node3_cert).mp (by decide +kernel))

def profile69_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node2 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13] 2 (by decide) (choices 3) [19] profile69_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,13] (choices 3) [19] profile69_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node3

def profile69_node4_cert : CutBound 5 := { lost := (rows 0 1 24 16 8), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 3, region := (rows 1 2 5 0 17), good := (rows 23 22 4 0 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile69_node4 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,28] 2 profile69_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30,28] 2 profile69_node4_cert).mp (by decide +kernel))

def profile69_node1_route : Route 5 := (fun mask => match mask with | 21 => (13,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile69_node1 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30] 2 (by decide) (choices 3) [13,28] profile69_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [30] (choices 3) [13,28] profile69_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile69_node2
  · exact profile69_node4

def profile69_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile69_node0 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [] 2 (by decide) (choices 4) [30] profile69_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [] (choices 4) [30] profile69_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile69_node1

theorem profile69 : Upper (D (n:=5) [66,52,52,34,34]) (R (n:=5) [66,52,52,34,34]) [] 2 := profile69_node0

def profile70_node3_cert : CutBound 5 := { lost := (rows 0 0 24 18 2), upper := (rows 31 31 7 13 29), lower := (rows 31 31 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile70_node3 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,3] 2 profile70_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,3] 2 profile70_node3_cert).mp (by decide +kernel))

def profile70_node4_cert : CutBound 5 := { lost := (rows 0 0 18 16 8), upper := (rows 31 31 13 15 23), lower := (rows 31 31 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile70_node4 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,9] 2 profile70_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29,9] 2 profile70_node4_cert).mp (by decide +kernel))

def profile70_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node2 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29] 2 (by decide) (choices 2) [3,9] profile70_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30,29] (choices 2) [3,9] profile70_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile70_node3
  · exact profile70_node4

def profile70_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node1 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30] 2 (by decide) (choices 4) [29] profile70_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [30] (choices 4) [29] profile70_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node2

def profile70_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile70_node0 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [] 2 (by decide) (choices 4) [30] profile70_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [] (choices 4) [30] profile70_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile70_node1

theorem profile70 : Upper (D (n:=5) [68,66,35,35,34]) (R (n:=5) [68,66,35,35,34]) [] 2 := profile70_node0

def profile71_node4_cert : CutBound 5 := { lost := (rows 0 0 8 4 3), upper := (rows 31 31 7 11 28), lower := (rows 31 31 7 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 27 11 11 16) },{ target := 3, region := (rows 1 2 15 0 16), good := (rows 23 23 7 7 16) }] }

theorem profile71_node4 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,3] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,3] 2 profile71_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,3] 2 profile71_node4_cert).mp (by decide +kernel))

def profile71_node5_cert : CutBound 5 := { lost := (rows 0 0 8 2 5), upper := (rows 31 31 7 13 26), lower := (rows 31 31 7 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 25 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 23 7 5 16) }] }

theorem profile71_node5 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,5] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,5] 2 profile71_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,5] 2 profile71_node5_cert).mp (by decide +kernel))

def profile71_node6_cert : CutBound 5 := { lost := (rows 0 0 8 1 6), upper := (rows 31 31 7 14 25), lower := (rows 31 31 7 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 26 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 23 7 6 16) }] }

theorem profile71_node6 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,6] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,6] 2 profile71_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3,6] 2 profile71_node6_cert).mp (by decide +kernel))

def profile71_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node3 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3] 2 (by decide) (choices 2) [3,5,6] profile71_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,3] (choices 2) [3,5,6] profile71_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile71_node4
  · exact profile71_node5
  · exact profile71_node6

def profile71_node7_cert : CutBound 5 := { lost := (rows 0 0 18 16 8), upper := (rows 31 31 13 15 23), lower := (rows 31 31 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile71_node7 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,9] 2 profile71_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,9] 2 profile71_node7_cert).mp (by decide +kernel))

def profile71_node8_cert : CutBound 5 := { lost := (rows 0 0 17 16 8), upper := (rows 31 31 14 15 23), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile71_node8 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,10] 2 profile71_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29,10] 2 profile71_node8_cert).mp (by decide +kernel))

def profile71_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node2 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29] 2 (by decide) (choices 2) [3,9,10] profile71_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30,29] (choices 2) [3,9,10] profile71_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile71_node3
  · exact profile71_node7
  · exact profile71_node8

def profile71_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node1 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30] 2 (by decide) (choices 4) [29] profile71_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [30] (choices 4) [29] profile71_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node2

def profile71_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile71_node0 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [] 2 (by decide) (choices 4) [30] profile71_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [] (choices 4) [30] profile71_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile71_node1

theorem profile71 : Upper (D (n:=5) [67,67,35,35,34]) (R (n:=5) [67,67,35,35,34]) [] 2 := profile71_node0

def profile72_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 13 13 29), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile72_node2 : Upper (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30,29] 2 profile72_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30,29] 2 profile72_node2_cert).mp (by decide +kernel))

def profile72_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node1 : Upper (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30] 2 (by decide) (choices 4) [29] profile72_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [30] (choices 4) [29] profile72_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node2

def profile72_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile72_node0 : Upper (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [] 2 (by decide) (choices 4) [30] profile72_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [] (choices 4) [30] profile72_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile72_node1

theorem profile72 : Upper (D (n:=5) [68,65,36,35,34]) (R (n:=5) [68,65,36,35,34]) [] 2 := profile72_node0

def profile73_node3_cert : CutBound 5 := { lost := (rows 0 0 24 18 2), upper := (rows 31 31 7 13 29), lower := (rows 31 31 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) },{ target := 3, region := (rows 1 2 7 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile73_node3 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,3] 2 :=
  cut_bound_sound (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,3] 2 profile73_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,3] 2 profile73_node3_cert).mp (by decide +kernel))

def profile73_node4_cert : CutBound 5 := { lost := (rows 0 0 18 16 8), upper := (rows 31 31 13 15 23), lower := (rows 31 31 13 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 13 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 13 8 0) }] }

theorem profile73_node4 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,9] 2 :=
  cut_bound_sound (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,9] 2 profile73_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,9] 2 profile73_node4_cert).mp (by decide +kernel))

def profile73_node5_cert : CutBound 5 := { lost := (rows 0 0 1 2 10), upper := (rows 31 31 14 13 21), lower := (rows 31 31 14 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 14 8 16) },{ target := 1, region := (rows 1 0 4 11 19), good := (rows 29 29 28 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile73_node5 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,10] 2 :=
  cut_bound_sound (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,10] 2 profile73_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29,10] 2 profile73_node5_cert).mp (by decide +kernel))

def profile73_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node2 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29] 2 (by decide) (choices 2) [3,9,10] profile73_node2_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30,29] (choices 2) [3,9,10] profile73_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile73_node3
  · exact profile73_node4
  · exact profile73_node5

def profile73_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node1 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30] 2 (by decide) (choices 4) [29] profile73_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [30] (choices 4) [29] profile73_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node2

def profile73_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile73_node0 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [] 2 (by decide) (choices 4) [30] profile73_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [] (choices 4) [30] profile73_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile73_node1

theorem profile73 : Upper (D (n:=5) [67,66,36,35,34]) (R (n:=5) [67,66,36,35,34]) [] 2 := profile73_node0

def profile74_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 27 15 11 27), lower := (rows 31 27 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile74_node2 : Upper (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30,25] 2 profile74_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30,25] 2 profile74_node2_cert).mp (by decide +kernel))

def profile74_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node1 : Upper (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30] 2 (by decide) (choices 3) [25] profile74_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [30] (choices 3) [25] profile74_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node2

def profile74_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile74_node0 : Upper (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [] 2 (by decide) (choices 4) [30] profile74_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [] (choices 4) [30] profile74_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile74_node1

theorem profile74 : Upper (D (n:=5) [68,52,49,35,34]) (R (n:=5) [68,52,49,35,34]) [] 2 := profile74_node0

def profile75_node3_cert : CutBound 5 := { lost := (rows 0 16 16 4 12), upper := (rows 31 15 15 27 19), lower := (rows 31 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile75_node3 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,11] 2 profile75_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,11] 2 profile75_node3_cert).mp (by decide +kernel))

def profile75_node4_cert : CutBound 5 := { lost := (rows 0 16 8 20 4), upper := (rows 31 15 23 11 27), lower := (rows 31 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile75_node4 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,19] 2 profile75_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,19] 2 profile75_node4_cert).mp (by decide +kernel))

def profile75_node5_cert : CutBound 5 := { lost := (rows 0 0 2 4 12), upper := (rows 31 15 29 11 19), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 25 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) }] }

theorem profile75_node5 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,25] 2 profile75_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13,25] 2 profile75_node5_cert).mp (by decide +kernel))

def profile75_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node2 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13] 2 (by decide) (choices 3) [11,19,25] profile75_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,13] (choices 3) [11,19,25] profile75_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node3
  · exact profile75_node4
  · exact profile75_node5

def profile75_node6_cert : CutBound 5 := { lost := (rows 0 8 16 20 4), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile75_node6 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,21] 2 profile75_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,21] 2 profile75_node6_cert).mp (by decide +kernel))

def profile75_node8_cert : CutBound 5 := { lost := (rows 0 4 16 16 8), upper := (rows 31 27 15 15 23), lower := (rows 31 27 15 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile75_node8 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25,11] 2 profile75_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25,11] 2 profile75_node8_cert).mp (by decide +kernel))

def profile75_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node7 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25] 2 (by decide) (choices 3) [11] profile75_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30,25] (choices 3) [11] profile75_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node8

def profile75_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node1 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30] 2 (by decide) (choices 3) [13,21,25] profile75_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [30] (choices 3) [13,21,25] profile75_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile75_node2
  · exact profile75_node6
  · exact profile75_node7

def profile75_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile75_node0 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [] 2 (by decide) (choices 4) [30] profile75_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [] (choices 4) [30] profile75_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile75_node1

theorem profile75 : Upper (D (n:=5) [68,51,50,35,34]) (R (n:=5) [68,51,50,35,34]) [] 2 := profile75_node0

def profile76_node3_cert : CutBound 5 := { lost := (rows 0 16 16 4 12), upper := (rows 31 15 15 27 19), lower := (rows 31 15 15 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node3 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,11] 2 profile76_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,11] 2 profile76_node3_cert).mp (by decide +kernel))

def profile76_node4_cert : CutBound 5 := { lost := (rows 0 16 8 20 4), upper := (rows 31 15 23 11 27), lower := (rows 31 15 23 8 16), losses := [{ target := 2, region := (rows 1 2 0 15 23), good := (rows 27 27 27 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node4 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,19] 2 profile76_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,19] 2 profile76_node4_cert).mp (by decide +kernel))

def profile76_node5_cert : CutBound 5 := { lost := (rows 0 0 1 4 12), upper := (rows 31 15 30 11 19), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 26 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) }] }

theorem profile76_node5 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,26] 2 profile76_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13,26] 2 profile76_node5_cert).mp (by decide +kernel))

def profile76_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node2 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13] 2 (by decide) (choices 3) [11,19,26] profile76_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,13] (choices 3) [11,19,26] profile76_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile76_node3
  · exact profile76_node4
  · exact profile76_node5

def profile76_node6_cert : CutBound 5 := { lost := (rows 0 8 16 20 4), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) },{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile76_node6 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,21] 2 profile76_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,21] 2 profile76_node6_cert).mp (by decide +kernel))

def profile76_node8_cert : CutBound 5 := { lost := (rows 0 4 16 16 8), upper := (rows 31 27 15 15 23), lower := (rows 31 27 15 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile76_node8 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25,11] 2 profile76_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25,11] 2 profile76_node8_cert).mp (by decide +kernel))

def profile76_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node7 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25] 2 (by decide) (choices 3) [11] profile76_node7_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,25] (choices 3) [11] profile76_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node8

def profile76_node9_cert : CutBound 5 := { lost := (rows 0 1 16 20 4), upper := (rows 31 30 15 11 27), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) },{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 26 0 8 16) },{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 14 4 8 0) }] }

theorem profile76_node9 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,28] 2 profile76_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30,28] 2 profile76_node9_cert).mp (by decide +kernel))

def profile76_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node1 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile76_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [30] (choices 3) [13,21,25,28] profile76_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile76_node2
  · exact profile76_node6
  · exact profile76_node7
  · exact profile76_node9

def profile76_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile76_node0 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [] 2 (by decide) (choices 4) [30] profile76_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [] (choices 4) [30] profile76_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile76_node1

theorem profile76 : Upper (D (n:=5) [67,52,50,35,34]) (R (n:=5) [67,52,50,35,34]) [] 2 := profile76_node0

def profile77_node4_cert : CutBound 5 := { lost := (rows 0 0 0 6 9), upper := (rows 31 15 15 25 22), lower := (rows 31 15 15 25 16), losses := [{ target := 0, region := (rows 0 2 4 8 23), good := (rows 30 30 30 24 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 25 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 25 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 17 16) }] }

theorem profile77_node4 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,17] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,17] 2 profile77_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,17] 2 profile77_node4_cert).mp (by decide +kernel))

def profile77_node5_cert : CutBound 5 := { lost := (rows 0 0 0 5 10), upper := (rows 31 15 15 26 21), lower := (rows 31 15 15 26 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 26 16) },{ target := 1, region := (rows 1 0 4 8 23), good := (rows 29 29 29 24 16) },{ target := 2, region := (rows 1 2 0 9 16), good := (rows 27 11 11 26 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 18 16) }] }

theorem profile77_node5 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,18] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,18] 2 profile77_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,18] 2 profile77_node5_cert).mp (by decide +kernel))

def profile77_node6_cert : CutBound 5 := { lost := (rows 0 0 0 3 12), upper := (rows 31 15 15 28 19), lower := (rows 31 15 15 28 16), losses := [{ target := 0, region := (rows 0 2 4 9 16), good := (rows 30 14 14 28 16) },{ target := 1, region := (rows 1 0 4 9 16), good := (rows 29 13 13 28 16) },{ target := 2, region := (rows 1 2 0 8 23), good := (rows 27 27 27 24 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 20 16) }] }

theorem profile77_node6 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,20] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,20] 2 profile77_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11,20] 2 profile77_node6_cert).mp (by decide +kernel))

def profile77_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node3 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11] 2 (by decide) (choices 2) [17,18,20] profile77_node3_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,11] (choices 2) [17,18,20] profile77_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node4
  · exact profile77_node5
  · exact profile77_node6

def profile77_node8_cert : CutBound 5 := { lost := (rows 0 0 8 4 3), upper := (rows 31 15 23 11 28), lower := (rows 31 15 23 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 26 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 11 27 11 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 7 16) }] }

theorem profile77_node8 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,3] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,3] 2 profile77_node8_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,3] 2 profile77_node8_cert).mp (by decide +kernel))

def profile77_node9_cert : CutBound 5 := { lost := (rows 0 0 8 2 5), upper := (rows 31 15 23 13 26), lower := (rows 31 15 23 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 19), good := (rows 30 30 22 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 13 29 13 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 25 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 5 16) }] }

theorem profile77_node9 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,5] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,5] 2 profile77_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,5] 2 profile77_node9_cert).mp (by decide +kernel))

def profile77_node10_cert : CutBound 5 := { lost := (rows 0 0 8 1 6), upper := (rows 31 15 23 14 25), lower := (rows 31 15 23 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 14 30 14 16) },{ target := 1, region := (rows 1 0 4 8 19), good := (rows 29 29 21 28 16) },{ target := 2, region := (rows 1 2 0 8 19), good := (rows 27 27 19 26 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 6 16) }] }

theorem profile77_node10 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,6] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,6] 2 profile77_node10_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19,6] 2 profile77_node10_cert).mp (by decide +kernel))

def profile77_node7_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node7 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19] 2 (by decide) (choices 2) [3,5,6] profile77_node7_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,19] (choices 2) [3,5,6] profile77_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node8
  · exact profile77_node9
  · exact profile77_node10

def profile77_node11_cert : CutBound 5 := { lost := (rows 0 16 2 16 8), upper := (rows 31 15 29 15 23), lower := (rows 31 15 29 8 16), losses := [{ target := 1, region := (rows 1 0 5 8 16), good := (rows 29 13 29 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 21 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node11 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,25] 2 profile77_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,25] 2 profile77_node11_cert).mp (by decide +kernel))

def profile77_node12_cert : CutBound 5 := { lost := (rows 0 16 1 16 8), upper := (rows 31 15 30 15 23), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile77_node12 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,26] 2 profile77_node12_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13,26] 2 profile77_node12_cert).mp (by decide +kernel))

def profile77_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node2 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13] 2 (by decide) (choices 3) [11,19,25,26] profile77_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,13] (choices 3) [11,19,25,26] profile77_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node3
  · exact profile77_node7
  · exact profile77_node11
  · exact profile77_node12

def profile77_node15_cert : CutBound 5 := { lost := (rows 0 8 0 4 3), upper := (rows 31 23 15 11 28), lower := (rows 31 23 15 11 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 26 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 25 16) },{ target := 2, region := (rows 1 2 0 15 16), good := (rows 27 27 11 11 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 3 16) }] }

theorem profile77_node15 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,3] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,3] 2 profile77_node15_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,3] 2 profile77_node15_cert).mp (by decide +kernel))

def profile77_node16_cert : CutBound 5 := { lost := (rows 0 8 0 2 5), upper := (rows 31 23 15 13 26), lower := (rows 31 23 15 13 16), losses := [{ target := 0, region := (rows 0 2 4 8 21), good := (rows 30 22 30 28 16) },{ target := 1, region := (rows 1 0 4 15 16), good := (rows 29 29 13 13 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 27 25 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 7 16) }] }

theorem profile77_node16 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,5] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,5] 2 profile77_node16_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,5] 2 profile77_node16_cert).mp (by decide +kernel))

def profile77_node17_cert : CutBound 5 := { lost := (rows 0 8 0 1 6), upper := (rows 31 23 15 14 25), lower := (rows 31 23 15 14 16), losses := [{ target := 0, region := (rows 0 2 4 15 16), good := (rows 30 30 14 14 16) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 29 21 29 28 16) },{ target := 2, region := (rows 1 2 0 8 21), good := (rows 27 19 27 26 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 6 16) }] }

theorem profile77_node17 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,6] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,6] 2 profile77_node17_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11,6] 2 profile77_node17_cert).mp (by decide +kernel))

def profile77_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node14 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11] 2 (by decide) (choices 2) [3,5,6] profile77_node14_route
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21,11] (choices 2) [3,5,6] profile77_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile77_node15
  · exact profile77_node16
  · exact profile77_node17

def profile77_node13_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node13 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21] 2 (by decide) (choices 3) [11] profile77_node13_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,21] (choices 3) [11] profile77_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node14

def profile77_node19_cert : CutBound 5 := { lost := (rows 0 4 16 16 8), upper := (rows 31 27 15 15 23), lower := (rows 31 27 15 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile77_node19 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25,11] 2 profile77_node19_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25,11] 2 profile77_node19_cert).mp (by decide +kernel))

def profile77_node18_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node18 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25] 2 (by decide) (choices 3) [11] profile77_node18_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,25] (choices 3) [11] profile77_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node19

def profile77_node21_cert : CutBound 5 := { lost := (rows 0 1 16 16 8), upper := (rows 31 30 15 15 23), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile77_node21 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28,11] 2 profile77_node21_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28,11] 2 profile77_node21_cert).mp (by decide +kernel))

def profile77_node20_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node20 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28] 2 (by decide) (choices 3) [11] profile77_node20_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30,28] (choices 3) [11] profile77_node20_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node21

def profile77_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node1 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile77_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [30] (choices 3) [13,21,25,28] profile77_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile77_node2
  · exact profile77_node13
  · exact profile77_node18
  · exact profile77_node20

def profile77_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile77_node0 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [] 2 (by decide) (choices 4) [30] profile77_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [] (choices 4) [30] profile77_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile77_node1

theorem profile77 : Upper (D (n:=5) [67,51,51,35,34]) (R (n:=5) [67,51,51,35,34]) [] 2 := profile77_node0

def profile78_node3_cert : CutBound 5 := { lost := (rows 0 16 16 1 9), upper := (rows 31 15 15 30 22), lower := (rows 31 15 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 4 0 23), good := (rows 23 23 23 0 16) },{ target := 4, region := (rows 1 7 7 8 0), good := (rows 15 15 15 8 0) }] }

theorem profile78_node3 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,11] 2 profile78_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,11] 2 profile78_node3_cert).mp (by decide +kernel))

def profile78_node4_cert : CutBound 5 := { lost := (rows 0 16 8 17 1), upper := (rows 31 15 23 14 30), lower := (rows 31 15 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 2 5 0 16), good := (rows 23 7 23 0 16) },{ target := 4, region := (rows 1 7 4 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile78_node4 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,19] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,19] 2 profile78_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,19] 2 profile78_node4_cert).mp (by decide +kernel))

def profile78_node5_cert : CutBound 5 := { lost := (rows 0 16 1 16 8), upper := (rows 31 15 30 15 23), lower := (rows 31 15 30 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 30 14 30 8 16) },{ target := 3, region := (rows 1 2 4 0 19), good := (rows 23 23 22 0 16) },{ target := 4, region := (rows 1 3 4 11 0), good := (rows 15 15 14 8 0) }] }

theorem profile78_node5 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,26] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,26] 2 profile78_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13,26] 2 profile78_node5_cert).mp (by decide +kernel))

def profile78_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node2 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13] 2 (by decide) (choices 3) [11,19,26] profile78_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,13] (choices 3) [11,19,26] profile78_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile78_node3
  · exact profile78_node4
  · exact profile78_node5

def profile78_node7_cert : CutBound 5 := { lost := (rows 0 8 16 17 1), upper := (rows 31 23 15 14 30), lower := (rows 31 23 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) },{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 7 0 16) },{ target := 4, region := (rows 1 2 7 15 0), good := (rows 15 15 15 8 0) }] }

theorem profile78_node7 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21,11] 2 profile78_node7_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21,11] 2 profile78_node7_cert).mp (by decide +kernel))

def profile78_node6_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node6 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21] 2 (by decide) (choices 3) [11] profile78_node6_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,21] (choices 3) [11] profile78_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node7

def profile78_node9_cert : CutBound 5 := { lost := (rows 0 4 0 1 9), upper := (rows 31 27 15 14 22), lower := (rows 31 27 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) },{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 11 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 19 23 0 16) }] }

theorem profile78_node9 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25,11] 2 profile78_node9_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25,11] 2 profile78_node9_cert).mp (by decide +kernel))

def profile78_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node8 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25] 2 (by decide) (choices 3) [11] profile78_node8_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,25] (choices 3) [11] profile78_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node9

def profile78_node11_cert : CutBound 5 := { lost := (rows 0 1 16 16 8), upper := (rows 31 30 15 15 23), lower := (rows 31 30 15 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 14 8 16) },{ target := 3, region := (rows 1 2 4 0 21), good := (rows 23 22 23 0 16) },{ target := 4, region := (rows 1 2 5 13 0), good := (rows 15 14 15 8 0) }] }

theorem profile78_node11 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28,11] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28,11] 2 profile78_node11_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28,11] 2 profile78_node11_cert).mp (by decide +kernel))

def profile78_node10_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node10 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28] 2 (by decide) (choices 3) [11] profile78_node10_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30,28] (choices 3) [11] profile78_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node11

def profile78_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node1 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile78_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [30] (choices 3) [13,21,25,28] profile78_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile78_node2
  · exact profile78_node6
  · exact profile78_node8
  · exact profile78_node10

def profile78_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile78_node0 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [] 2 (by decide) (choices 4) [30] profile78_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [] (choices 4) [30] profile78_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile78_node1

theorem profile78 : Upper (D (n:=5) [66,52,51,35,34]) (R (n:=5) [66,52,51,35,34]) [] 2 := profile78_node0

#print axioms profile78
end Delivery.FiveVertexPositive14
