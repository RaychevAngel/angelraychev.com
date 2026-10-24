import FiveVertexPositiveBase

namespace Delivery.FiveVertexPositive14
open FiniteGame Extremal RowPrefix SmallBudgetProfiles FiveVertexPositiveBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 7 11 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30,29] 2 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30,29] 2 profile0_node2_cert).mp (by decide +kernel))

def profile0_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30] 2 (by decide) (choices 4) [29] profile0_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [30] (choices 4) [29] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node2

def profile0_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [] 2 (by decide) (choices 4) [30] profile0_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [] (choices 4) [30] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=5) [68,68,50,34,18]) (R (n:=5) [68,68,50,34,18]) [] 2 := profile0_node0

def profile1_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile1_node2 : Upper (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30,29] 2 profile1_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30,29] 2 profile1_node2_cert).mp (by decide +kernel))

def profile1_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30] 2 (by decide) (choices 4) [29] profile1_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [30] (choices 4) [29] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [] 2 (by decide) (choices 4) [30] profile1_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [] (choices 4) [30] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=5) [68,67,51,34,18]) (R (n:=5) [68,67,51,34,18]) [] 2 := profile1_node0

def profile2_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile2_node2 : Upper (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30,29] 2 profile2_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30,29] 2 profile2_node2_cert).mp (by decide +kernel))

def profile2_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30] 2 (by decide) (choices 4) [29] profile2_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [30] (choices 4) [29] profile2_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node2

def profile2_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [] 2 (by decide) (choices 4) [30] profile2_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [] (choices 4) [30] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [68,66,52,34,18]) (R (n:=5) [68,66,52,34,18]) [] 2 := profile2_node0

def profile3_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 7 15 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile3_node2 : Upper (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30,29] 2 profile3_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30,29] 2 profile3_node2_cert).mp (by decide +kernel))

def profile3_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30] 2 (by decide) (choices 4) [29] profile3_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [30] (choices 4) [29] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [] 2 (by decide) (choices 4) [30] profile3_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [] (choices 4) [30] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node1

theorem profile3 : Upper (D (n:=5) [67,67,52,34,18]) (R (n:=5) [67,67,52,34,18]) [] 2 := profile3_node0

def profile4_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 15 11 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile4_node2 : Upper (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30,29] 2 profile4_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30,29] 2 profile4_node2_cert).mp (by decide +kernel))

def profile4_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node1 : Upper (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30] 2 (by decide) (choices 4) [29] profile4_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [30] (choices 4) [29] profile4_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node2

def profile4_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [] 2 (by decide) (choices 4) [30] profile4_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [] (choices 4) [30] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node1

theorem profile4 : Upper (D (n:=5) [68,67,50,35,18]) (R (n:=5) [68,67,50,35,18]) [] 2 := profile4_node0

def profile5_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile5_node2 : Upper (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30,29] 2 profile5_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30,29] 2 profile5_node2_cert).mp (by decide +kernel))

def profile5_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node1 : Upper (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30] 2 (by decide) (choices 4) [29] profile5_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [30] (choices 4) [29] profile5_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node2

def profile5_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [] 2 (by decide) (choices 4) [30] profile5_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [] (choices 4) [30] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile5_node1

theorem profile5 : Upper (D (n:=5) [68,66,51,35,18]) (R (n:=5) [68,66,51,35,18]) [] 2 := profile5_node0

def profile6_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile6_node2 : Upper (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30,29] 2 profile6_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30,29] 2 profile6_node2_cert).mp (by decide +kernel))

def profile6_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node1 : Upper (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30] 2 (by decide) (choices 4) [29] profile6_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [30] (choices 4) [29] profile6_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node2

def profile6_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [] 2 (by decide) (choices 4) [30] profile6_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [] (choices 4) [30] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node1

theorem profile6 : Upper (D (n:=5) [67,67,51,35,18]) (R (n:=5) [67,67,51,35,18]) [] 2 := profile6_node0

def profile7_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile7_node2 : Upper (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30,29] 2 profile7_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30,29] 2 profile7_node2_cert).mp (by decide +kernel))

def profile7_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node1 : Upper (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30] 2 (by decide) (choices 4) [29] profile7_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [30] (choices 4) [29] profile7_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node2

def profile7_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [] 2 (by decide) (choices 4) [30] profile7_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [] (choices 4) [30] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile7_node1

theorem profile7 : Upper (D (n:=5) [67,66,52,35,18]) (R (n:=5) [67,66,52,35,18]) [] 2 := profile7_node0

def profile8_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 15 11 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile8_node2 : Upper (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30,29] 2 profile8_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30,29] 2 profile8_node2_cert).mp (by decide +kernel))

def profile8_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node1 : Upper (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30] 2 (by decide) (choices 4) [29] profile8_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [30] (choices 4) [29] profile8_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node2

def profile8_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [] 2 (by decide) (choices 4) [30] profile8_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [] (choices 4) [30] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile8_node1

theorem profile8 : Upper (D (n:=5) [68,66,50,36,18]) (R (n:=5) [68,66,50,36,18]) [] 2 := profile8_node0

def profile9_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 15 11 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile9_node2 : Upper (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30,29] 2 profile9_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30,29] 2 profile9_node2_cert).mp (by decide +kernel))

def profile9_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30] 2 (by decide) (choices 4) [29] profile9_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [30] (choices 4) [29] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node2

def profile9_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [] 2 (by decide) (choices 4) [30] profile9_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [] (choices 4) [30] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=5) [67,67,50,36,18]) (R (n:=5) [67,67,50,36,18]) [] 2 := profile9_node0

def profile10_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile10_node2 : Upper (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30,29] 2 profile10_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30,29] 2 profile10_node2_cert).mp (by decide +kernel))

def profile10_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node1 : Upper (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30] 2 (by decide) (choices 4) [29] profile10_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [30] (choices 4) [29] profile10_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node2

def profile10_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [] 2 (by decide) (choices 4) [30] profile10_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [] (choices 4) [30] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=5) [67,66,51,36,18]) (R (n:=5) [67,66,51,36,18]) [] 2 := profile10_node0

def profile11_node2_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 31 31 15 15 31), lower := (rows 31 31 4 8 16), losses := [{ target := 4, region := (rows 1 2 7 11 0), good := (rows 15 15 4 8 0) }] }

theorem profile11_node2 : Upper (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30,29] 2 profile11_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30,29] 2 profile11_node2_cert).mp (by decide +kernel))

def profile11_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node1 : Upper (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30] 2 (by decide) (choices 4) [29] profile11_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [30] (choices 4) [29] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node2

def profile11_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile11_node0 : Upper (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [] 2 (by decide) (choices 4) [30] profile11_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [] (choices 4) [30] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node1

theorem profile11 : Upper (D (n:=5) [66,66,52,36,18]) (R (n:=5) [66,66,52,36,18]) [] 2 := profile11_node0

def profile12_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile12_node2 : Upper (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,13] 2 profile12_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,13] 2 profile12_node2_cert).mp (by decide +kernel))

def profile12_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 15 11 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile12_node3 : Upper (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,21] 2 profile12_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30,21] 2 profile12_node3_cert).mp (by decide +kernel))

def profile12_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile12_node1 : Upper (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30] 2 (by decide) (choices 3) [13,21] profile12_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [30] (choices 3) [13,21] profile12_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node2
  · exact profile12_node3

def profile12_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile12_node0 : Upper (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [] 2 (by decide) (choices 4) [30] profile12_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [] (choices 4) [30] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile12_node1

theorem profile12 : Upper (D (n:=5) [68,52,50,50,18]) (R (n:=5) [68,52,50,50,18]) [] 2 := profile12_node0

def profile13_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile13_node2 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,13] 2 profile13_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,13] 2 profile13_node2_cert).mp (by decide +kernel))

def profile13_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile13_node3 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,21] 2 profile13_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,21] 2 profile13_node3_cert).mp (by decide +kernel))

def profile13_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile13_node4 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,25] 2 profile13_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30,25] 2 profile13_node4_cert).mp (by decide +kernel))

def profile13_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node1 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30] 2 (by decide) (choices 3) [13,21,25] profile13_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [30] (choices 3) [13,21,25] profile13_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node2
  · exact profile13_node3
  · exact profile13_node4

def profile13_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [] 2 (by decide) (choices 4) [30] profile13_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [] (choices 4) [30] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node1

theorem profile13 : Upper (D (n:=5) [68,51,51,50,18]) (R (n:=5) [68,51,51,50,18]) [] 2 := profile13_node0

def profile14_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile14_node2 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,13] 2 profile14_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,13] 2 profile14_node2_cert).mp (by decide +kernel))

def profile14_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile14_node3 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,21] 2 profile14_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,21] 2 profile14_node3_cert).mp (by decide +kernel))

def profile14_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 7 15 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile14_node4 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,25] 2 profile14_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,25] 2 profile14_node4_cert).mp (by decide +kernel))

def profile14_node5_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile14_node5 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,28] 2 profile14_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30,28] 2 profile14_node5_cert).mp (by decide +kernel))

def profile14_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile14_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [30] (choices 3) [13,21,25,28] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node3
  · exact profile14_node4
  · exact profile14_node5

def profile14_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [] 2 (by decide) (choices 4) [30] profile14_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [] (choices 4) [30] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node1

theorem profile14 : Upper (D (n:=5) [67,52,51,50,18]) (R (n:=5) [67,52,51,50,18]) [] 2 := profile14_node0

def profile15_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile15_node2 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,13] 2 profile15_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,13] 2 profile15_node2_cert).mp (by decide +kernel))

def profile15_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile15_node3 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,21] 2 profile15_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,21] 2 profile15_node3_cert).mp (by decide +kernel))

def profile15_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 7 15 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile15_node4 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,28] 2 profile15_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30,28] 2 profile15_node4_cert).mp (by decide +kernel))

def profile15_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile15_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [30] (choices 3) [13,21,28] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node2
  · exact profile15_node3
  · exact profile15_node4

def profile15_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [] 2 (by decide) (choices 4) [30] profile15_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [] (choices 4) [30] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node1

theorem profile15 : Upper (D (n:=5) [66,52,52,50,18]) (R (n:=5) [66,52,52,50,18]) [] 2 := profile15_node0

def profile16_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 31 31 31), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile16_node2 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,13] 2 profile16_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,13] 2 profile16_node2_cert).mp (by decide +kernel))

def profile16_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile16_node3 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,21] 2 profile16_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,21] 2 profile16_node3_cert).mp (by decide +kernel))

def profile16_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile16_node4 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,28] 2 profile16_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30,28] 2 profile16_node4_cert).mp (by decide +kernel))

def profile16_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile16_node1 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile16_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [30] (choices 3) [13,21,28] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile16_node2
  · exact profile16_node3
  · exact profile16_node4

def profile16_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile16_node0 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [] 2 (by decide) (choices 4) [30] profile16_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [] (choices 4) [30] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node1

theorem profile16 : Upper (D (n:=5) [67,51,51,51,18]) (R (n:=5) [67,51,51,51,18]) [] 2 := profile16_node0

def profile17_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 31 31 31), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile17_node2 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,13] 2 profile17_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,13] 2 profile17_node2_cert).mp (by decide +kernel))

def profile17_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 15 15 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile17_node3 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,21] 2 profile17_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,21] 2 profile17_node3_cert).mp (by decide +kernel))

def profile17_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 15 15 31), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile17_node4 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,28] 2 profile17_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30,28] 2 profile17_node4_cert).mp (by decide +kernel))

def profile17_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile17_node1 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30] 2 (by decide) (choices 3) [13,21,28] profile17_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [30] (choices 3) [13,21,28] profile17_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile17_node2
  · exact profile17_node3
  · exact profile17_node4

def profile17_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile17_node0 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [] 2 (by decide) (choices 4) [30] profile17_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [] (choices 4) [30] profile17_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile17_node1

theorem profile17 : Upper (D (n:=5) [66,52,51,51,18]) (R (n:=5) [66,52,51,51,18]) [] 2 := profile17_node0

def profile18_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile18_node2 : Upper (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30,29] 2 profile18_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30,29] 2 profile18_node2_cert).mp (by decide +kernel))

def profile18_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node1 : Upper (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30] 2 (by decide) (choices 4) [29] profile18_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [30] (choices 4) [29] profile18_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node2

def profile18_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile18_node0 : Upper (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [] 2 (by decide) (choices 4) [30] profile18_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [] (choices 4) [30] profile18_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile18_node1

theorem profile18 : Upper (D (n:=5) [68,67,50,34,19]) (R (n:=5) [68,67,50,34,19]) [] 2 := profile18_node0

def profile19_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 23 31 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile19_node2 : Upper (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30,29] 2 profile19_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30,29] 2 profile19_node2_cert).mp (by decide +kernel))

def profile19_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node1 : Upper (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30] 2 (by decide) (choices 4) [29] profile19_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [30] (choices 4) [29] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node2

def profile19_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [] 2 (by decide) (choices 4) [30] profile19_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [] (choices 4) [30] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=5) [68,66,51,34,19]) (R (n:=5) [68,66,51,34,19]) [] 2 := profile19_node0

def profile20_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 23 31 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile20_node2 : Upper (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30,29] 2 profile20_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30,29] 2 profile20_node2_cert).mp (by decide +kernel))

def profile20_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node1 : Upper (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30] 2 (by decide) (choices 4) [29] profile20_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [30] (choices 4) [29] profile20_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node2

def profile20_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile20_node0 : Upper (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [] 2 (by decide) (choices 4) [30] profile20_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [] (choices 4) [30] profile20_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile20_node1

theorem profile20 : Upper (D (n:=5) [67,67,51,34,19]) (R (n:=5) [67,67,51,34,19]) [] 2 := profile20_node0

def profile21_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 23 31 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile21_node2 : Upper (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30,29] 2 profile21_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30,29] 2 profile21_node2_cert).mp (by decide +kernel))

def profile21_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30] 2 (by decide) (choices 4) [29] profile21_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [30] (choices 4) [29] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node2

def profile21_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [] 2 (by decide) (choices 4) [30] profile21_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [] (choices 4) [30] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node1

theorem profile21 : Upper (D (n:=5) [67,66,52,34,19]) (R (n:=5) [67,66,52,34,19]) [] 2 := profile21_node0

def profile22_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 31 27 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile22_node2 : Upper (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30,29] 2 profile22_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30,29] 2 profile22_node2_cert).mp (by decide +kernel))

def profile22_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node1 : Upper (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30] 2 (by decide) (choices 4) [29] profile22_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [30] (choices 4) [29] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node2

def profile22_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [] 2 (by decide) (choices 4) [30] profile22_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [] (choices 4) [30] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=5) [68,66,50,35,19]) (R (n:=5) [68,66,50,35,19]) [] 2 := profile22_node0

def profile23_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 31 27 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile23_node2 : Upper (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30,29] 2 profile23_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30,29] 2 profile23_node2_cert).mp (by decide +kernel))

def profile23_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node1 : Upper (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30] 2 (by decide) (choices 4) [29] profile23_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [30] (choices 4) [29] profile23_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node2

def profile23_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [] 2 (by decide) (choices 4) [30] profile23_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [] (choices 4) [30] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile23_node1

theorem profile23 : Upper (D (n:=5) [67,67,50,35,19]) (R (n:=5) [67,67,50,35,19]) [] 2 := profile23_node0

def profile24_node3_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 31 15 29 21), lower := (rows 31 31 15 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile24_node3 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,11] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,11] 2 profile24_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,11] 2 profile24_node3_cert).mp (by decide +kernel))

def profile24_node4_cert : CutBound 5 := { lost := (rows 0 0 0 2 0), upper := (rows 31 31 23 13 29), lower := (rows 31 31 23 8 16), losses := [{ target := 1, region := (rows 1 0 4 15 23), good := (rows 29 29 29 8 16) }] }

theorem profile24_node4 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,19] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,19] 2 profile24_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,19] 2 profile24_node4_cert).mp (by decide +kernel))

def profile24_node5_cert : CutBound 5 := { lost := (rows 0 0 2 0 0), upper := (rows 31 31 29 15 23), lower := (rows 31 31 29 8 16), losses := [{ target := 1, region := (rows 1 0 7 8 16), good := (rows 29 29 29 8 16) }] }

theorem profile24_node5 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,25] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,25] 2 profile24_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,25] 2 profile24_node5_cert).mp (by decide +kernel))

def profile24_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 30 13 21), lower := (rows 31 31 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile24_node6 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,26] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,26] 2 profile24_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29,26] 2 profile24_node6_cert).mp (by decide +kernel))

def profile24_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node2 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29] 2 (by decide) (choices 3) [11,19,25,26] profile24_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30,29] (choices 3) [11,19,25,26] profile24_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile24_node3
  · exact profile24_node4
  · exact profile24_node5
  · exact profile24_node6

def profile24_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30] 2 (by decide) (choices 4) [29] profile24_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [30] (choices 4) [29] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node2

def profile24_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [] 2 (by decide) (choices 4) [30] profile24_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [] (choices 4) [30] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=5) [67,66,51,35,19]) (R (n:=5) [67,66,51,35,19]) [] 2 := profile24_node0

def profile25_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 15 28 20), lower := (rows 31 31 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile25_node3 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,11] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,11] 2 profile25_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,11] 2 profile25_node3_cert).mp (by decide +kernel))

def profile25_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 23 12 28), lower := (rows 31 31 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile25_node4 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,19] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,19] 2 profile25_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,19] 2 profile25_node4_cert).mp (by decide +kernel))

def profile25_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 29 14 22), lower := (rows 31 31 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile25_node5 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,25] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,25] 2 profile25_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,25] 2 profile25_node5_cert).mp (by decide +kernel))

def profile25_node6_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 30 13 21), lower := (rows 31 31 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile25_node6 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,26] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,26] 2 profile25_node6_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29,26] 2 profile25_node6_cert).mp (by decide +kernel))

def profile25_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node2 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29] 2 (by decide) (choices 3) [11,19,25,26] profile25_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30,29] (choices 3) [11,19,25,26] profile25_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile25_node3
  · exact profile25_node4
  · exact profile25_node5
  · exact profile25_node6

def profile25_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node1 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30] 2 (by decide) (choices 4) [29] profile25_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [30] (choices 4) [29] profile25_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node2

def profile25_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile25_node0 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [] 2 (by decide) (choices 4) [30] profile25_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [] (choices 4) [30] profile25_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile25_node1

theorem profile25 : Upper (D (n:=5) [66,66,52,35,19]) (R (n:=5) [66,66,52,35,19]) [] 2 := profile25_node0

def profile26_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 31 27 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile26_node2 : Upper (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30,29] 2 profile26_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30,29] 2 profile26_node2_cert).mp (by decide +kernel))

def profile26_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node1 : Upper (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30] 2 (by decide) (choices 4) [29] profile26_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [30] (choices 4) [29] profile26_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node2

def profile26_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile26_node0 : Upper (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [] 2 (by decide) (choices 4) [30] profile26_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [] (choices 4) [30] profile26_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile26_node1

theorem profile26 : Upper (D (n:=5) [67,66,50,36,19]) (R (n:=5) [67,66,50,36,19]) [] 2 := profile26_node0

def profile27_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 15 28 28), lower := (rows 31 31 15 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile27_node3 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,11] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,11] 2 profile27_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,11] 2 profile27_node3_cert).mp (by decide +kernel))

def profile27_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 29 14 30), lower := (rows 31 31 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile27_node4 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,25] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,25] 2 profile27_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,25] 2 profile27_node4_cert).mp (by decide +kernel))

def profile27_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 30 13 29), lower := (rows 31 31 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile27_node5 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,26] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,26] 2 profile27_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29,26] 2 profile27_node5_cert).mp (by decide +kernel))

def profile27_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node2 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29] 2 (by decide) (choices 3) [11,25,26] profile27_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30,29] (choices 3) [11,25,26] profile27_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile27_node3
  · exact profile27_node4
  · exact profile27_node5

def profile27_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30] 2 (by decide) (choices 4) [29] profile27_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [30] (choices 4) [29] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node2

def profile27_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [] 2 (by decide) (choices 4) [30] profile27_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [] (choices 4) [30] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=5) [66,66,51,36,19]) (R (n:=5) [66,66,51,36,19]) [] 2 := profile27_node0

def profile28_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile28_node2 : Upper (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,13] 2 profile28_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,13] 2 profile28_node2_cert).mp (by decide +kernel))

def profile28_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile28_node3 : Upper (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,21] 2 profile28_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30,21] 2 profile28_node3_cert).mp (by decide +kernel))

def profile28_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile28_node1 : Upper (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30] 2 (by decide) (choices 3) [13,21] profile28_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [30] (choices 3) [13,21] profile28_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node2
  · exact profile28_node3

def profile28_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [] 2 (by decide) (choices 4) [30] profile28_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [] (choices 4) [30] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node1

theorem profile28 : Upper (D (n:=5) [68,51,50,50,19]) (R (n:=5) [68,51,50,50,19]) [] 2 := profile28_node0

def profile29_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 15 23 27 19), lower := (rows 31 15 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile29_node2 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,13] 2 profile29_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,13] 2 profile29_node2_cert).mp (by decide +kernel))

def profile29_node3_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile29_node3 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,21] 2 profile29_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,21] 2 profile29_node3_cert).mp (by decide +kernel))

def profile29_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile29_node4 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,28] 2 profile29_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30,28] 2 profile29_node4_cert).mp (by decide +kernel))

def profile29_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile29_node1 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile29_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [30] (choices 3) [13,21,28] profile29_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile29_node2
  · exact profile29_node3
  · exact profile29_node4

def profile29_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile29_node0 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [] 2 (by decide) (choices 4) [30] profile29_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [] (choices 4) [30] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node1

theorem profile29 : Upper (D (n:=5) [67,52,50,50,19]) (R (n:=5) [67,52,50,50,19]) [] 2 := profile29_node0

def profile30_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile30_node2 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,13] 2 profile30_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,13] 2 profile30_node2_cert).mp (by decide +kernel))

def profile30_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 31 31 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile30_node3 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,21] 2 profile30_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,21] 2 profile30_node3_cert).mp (by decide +kernel))

def profile30_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile30_node4 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,25] 2 profile30_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,25] 2 profile30_node4_cert).mp (by decide +kernel))

def profile30_node5_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile30_node5 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,28] 2 profile30_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30,28] 2 profile30_node5_cert).mp (by decide +kernel))

def profile30_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node1 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile30_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [30] (choices 3) [13,21,25,28] profile30_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile30_node2
  · exact profile30_node3
  · exact profile30_node4
  · exact profile30_node5

def profile30_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile30_node0 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [] 2 (by decide) (choices 4) [30] profile30_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [] (choices 4) [30] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile30_node1

theorem profile30 : Upper (D (n:=5) [67,51,51,50,19]) (R (n:=5) [67,51,51,50,19]) [] 2 := profile30_node0

def profile31_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 15 23 31 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile31_node2 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,13] 2 profile31_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,13] 2 profile31_node2_cert).mp (by decide +kernel))

def profile31_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 31 31 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile31_node3 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,21] 2 profile31_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,21] 2 profile31_node3_cert).mp (by decide +kernel))

def profile31_node4_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile31_node4 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,25] 2 profile31_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,25] 2 profile31_node4_cert).mp (by decide +kernel))

def profile31_node5_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile31_node5 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,28] 2 profile31_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30,28] 2 profile31_node5_cert).mp (by decide +kernel))

def profile31_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node1 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30] 2 (by decide) (choices 3) [13,21,25,28] profile31_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [30] (choices 3) [13,21,25,28] profile31_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile31_node2
  · exact profile31_node3
  · exact profile31_node4
  · exact profile31_node5

def profile31_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile31_node0 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [] 2 (by decide) (choices 4) [30] profile31_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [] (choices 4) [30] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile31_node1

theorem profile31 : Upper (D (n:=5) [66,52,51,50,19]) (R (n:=5) [66,52,51,50,19]) [] 2 := profile31_node0

def profile32_node2_cert : CutBound 5 := { lost := (rows 0 16 0 0 0), upper := (rows 31 15 31 31 31), lower := (rows 31 15 4 8 16), losses := [{ target := 4, region := (rows 1 3 4 8 0), good := (rows 15 15 4 8 0) }] }

theorem profile32_node2 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,13] 2 profile32_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,13] 2 profile32_node2_cert).mp (by decide +kernel))

def profile32_node3_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 31 31 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile32_node3 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,21] 2 profile32_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,21] 2 profile32_node3_cert).mp (by decide +kernel))

def profile32_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 31 31 31), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile32_node4 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,28] 2 profile32_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30,28] 2 profile32_node4_cert).mp (by decide +kernel))

def profile32_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile32_node1 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30] 2 (by decide) (choices 3) [13,21,28] profile32_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [30] (choices 3) [13,21,28] profile32_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile32_node2
  · exact profile32_node3
  · exact profile32_node4

def profile32_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile32_node0 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [] 2 (by decide) (choices 4) [30] profile32_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [] (choices 4) [30] profile32_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node1

theorem profile32 : Upper (D (n:=5) [66,51,51,51,19]) (R (n:=5) [66,51,51,51,19]) [] 2 := profile32_node0

def profile33_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile33_node2 : Upper (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30,29] 2 profile33_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30,29] 2 profile33_node2_cert).mp (by decide +kernel))

def profile33_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node1 : Upper (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30] 2 (by decide) (choices 4) [29] profile33_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [30] (choices 4) [29] profile33_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node2

def profile33_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile33_node0 : Upper (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [] 2 (by decide) (choices 4) [30] profile33_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [] (choices 4) [30] profile33_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile33_node1

theorem profile33 : Upper (D (n:=5) [68,66,50,34,20]) (R (n:=5) [68,66,50,34,20]) [] 2 := profile33_node0

def profile34_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 23 27 19), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile34_node2 : Upper (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30,29] 2 profile34_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30,29] 2 profile34_node2_cert).mp (by decide +kernel))

def profile34_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node1 : Upper (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30] 2 (by decide) (choices 4) [29] profile34_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [30] (choices 4) [29] profile34_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node2

def profile34_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile34_node0 : Upper (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [] 2 (by decide) (choices 4) [30] profile34_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [] (choices 4) [30] profile34_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile34_node1

theorem profile34 : Upper (D (n:=5) [67,67,50,34,20]) (R (n:=5) [67,67,50,34,20]) [] 2 := profile34_node0

def profile35_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 23 31 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile35_node2 : Upper (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30,29] 2 profile35_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30,29] 2 profile35_node2_cert).mp (by decide +kernel))

def profile35_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node1 : Upper (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30] 2 (by decide) (choices 4) [29] profile35_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [30] (choices 4) [29] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node2

def profile35_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile35_node0 : Upper (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [] 2 (by decide) (choices 4) [30] profile35_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [] (choices 4) [30] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=5) [67,66,51,34,20]) (R (n:=5) [67,66,51,34,20]) [] 2 := profile35_node0

def profile36_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 0), upper := (rows 31 31 23 31 23), lower := (rows 31 31 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile36_node2 : Upper (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30,29] 2 profile36_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30,29] 2 profile36_node2_cert).mp (by decide +kernel))

def profile36_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30] 2 (by decide) (choices 4) [29] profile36_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [30] (choices 4) [29] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node2

def profile36_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile36_node0 : Upper (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [] 2 (by decide) (choices 4) [30] profile36_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [] (choices 4) [30] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node1

theorem profile36 : Upper (D (n:=5) [66,66,52,34,20]) (R (n:=5) [66,66,52,34,20]) [] 2 := profile36_node0

def profile37_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 31 27 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile37_node2 : Upper (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30,29] 2 profile37_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30,29] 2 profile37_node2_cert).mp (by decide +kernel))

def profile37_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30] 2 (by decide) (choices 4) [29] profile37_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [30] (choices 4) [29] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node2

def profile37_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile37_node0 : Upper (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [] 2 (by decide) (choices 4) [30] profile37_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [] (choices 4) [30] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=5) [67,66,50,35,20]) (R (n:=5) [67,66,50,35,20]) [] 2 := profile37_node0

def profile38_node3_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 23 28 28), lower := (rows 31 31 23 8 16), losses := [{ target := 0, region := (rows 0 2 4 15 23), good := (rows 30 30 30 8 16) }] }

theorem profile38_node3 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,19] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,19] 2 profile38_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,19] 2 profile38_node3_cert).mp (by decide +kernel))

def profile38_node4_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 31 31 29 30 22), lower := (rows 31 31 29 8 16), losses := [{ target := 0, region := (rows 0 2 4 11 19), good := (rows 30 30 28 8 16) }] }

theorem profile38_node4 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,25] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,25] 2 profile38_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,25] 2 profile38_node4_cert).mp (by decide +kernel))

def profile38_node5_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 31 31 30 29 21), lower := (rows 31 31 30 8 16), losses := [{ target := 0, region := (rows 0 2 7 8 16), good := (rows 30 30 30 8 16) }] }

theorem profile38_node5 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,26] 2 :=
  cut_bound_sound (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,26] 2 profile38_node5_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29,26] 2 profile38_node5_cert).mp (by decide +kernel))

def profile38_node2_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node2 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29] 2 (by decide) (choices 3) [19,25,26] profile38_node2_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30,29] (choices 3) [19,25,26] profile38_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node3
  · exact profile38_node4
  · exact profile38_node5

def profile38_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30] 2 (by decide) (choices 4) [29] profile38_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [30] (choices 4) [29] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node2

def profile38_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile38_node0 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [] 2 (by decide) (choices 4) [30] profile38_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [] (choices 4) [30] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node1

theorem profile38 : Upper (D (n:=5) [66,66,51,35,20]) (R (n:=5) [66,66,51,35,20]) [] 2 := profile38_node0

def profile39_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 31 31 27 27), lower := (rows 31 31 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile39_node2 : Upper (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30,29] 2 :=
  cut_bound_sound (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30,29] 2 profile39_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30,29] 2 profile39_node2_cert).mp (by decide +kernel))

def profile39_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node1 : Upper (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30] 2 (by decide) (choices 4) [29] profile39_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [30] (choices 4) [29] profile39_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node2

def profile39_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile39_node0 : Upper (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [] 2 (by decide) (choices 4) [30] profile39_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [] (choices 4) [30] profile39_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node1

theorem profile39 : Upper (D (n:=5) [66,66,50,36,20]) (R (n:=5) [66,66,50,36,20]) [] 2 := profile39_node0

def profile40_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile40_node2 : Upper (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30,21] 2 profile40_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30,21] 2 profile40_node2_cert).mp (by decide +kernel))

def profile40_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile40_node1 : Upper (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30] 2 (by decide) (choices 3) [21] profile40_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [30] (choices 3) [21] profile40_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node2

def profile40_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile40_node0 : Upper (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [] 2 := by
  apply routed_branch (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [] 2 (by decide) (choices 4) [30] profile40_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [] (choices 4) [30] profile40_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node1

theorem profile40 : Upper (D (n:=5) [68,50,50,50,20]) (R (n:=5) [68,50,50,50,20]) [] 2 := profile40_node0

def profile41_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile41_node2 : Upper (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,21] 2 profile41_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,21] 2 profile41_node2_cert).mp (by decide +kernel))

def profile41_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile41_node3 : Upper (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,28] 2 profile41_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30,28] 2 profile41_node3_cert).mp (by decide +kernel))

def profile41_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile41_node1 : Upper (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30] 2 (by decide) (choices 3) [21,28] profile41_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [30] (choices 3) [21,28] profile41_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node2
  · exact profile41_node3

def profile41_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile41_node0 : Upper (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [] 2 := by
  apply routed_branch (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [] 2 (by decide) (choices 4) [30] profile41_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [] (choices 4) [30] profile41_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node1

theorem profile41 : Upper (D (n:=5) [67,51,50,50,20]) (R (n:=5) [67,51,50,50,20]) [] 2 := profile41_node0

def profile42_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 31 23 31 27 27), lower := (rows 31 23 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile42_node2 : Upper (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,21] 2 profile42_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,21] 2 profile42_node2_cert).mp (by decide +kernel))

def profile42_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 27 19), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile42_node3 : Upper (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,28] 2 profile42_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30,28] 2 profile42_node3_cert).mp (by decide +kernel))

def profile42_node1_route : Route 5 := (fun mask => match mask with | 25 => (21,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile42_node1 : Upper (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30] 2 (by decide) (choices 3) [21,28] profile42_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [30] (choices 3) [21,28] profile42_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile42_node2
  · exact profile42_node3

def profile42_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile42_node0 : Upper (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [] 2 (by decide) (choices 4) [30] profile42_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [] (choices 4) [30] profile42_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=5) [66,52,50,50,20]) (R (n:=5) [66,52,50,50,20]) [] 2 := profile42_node0

def profile43_node2_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 31 23 31 31 31), lower := (rows 31 23 4 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 16), good := (rows 23 23 4 0 16) }] }

theorem profile43_node2 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,21] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,21] 2 profile43_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,21] 2 profile43_node2_cert).mp (by decide +kernel))

def profile43_node3_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 31 27 23 31 23), lower := (rows 31 27 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 27 27 0 8 16) }] }

theorem profile43_node3 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,25] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,25] 2 profile43_node3_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,25] 2 profile43_node3_cert).mp (by decide +kernel))

def profile43_node4_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 31 30 23 31 23), lower := (rows 31 30 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 30 30 4 8 16) }] }

theorem profile43_node4 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,28] 2 :=
  cut_bound_sound (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,28] 2 profile43_node4_cert
    ((SmallCut.boundCheck_true (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30,28] 2 profile43_node4_cert).mp (by decide +kernel))

def profile43_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node1 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30] 2 (by decide) (choices 3) [21,25,28] profile43_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [30] (choices 3) [21,25,28] profile43_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile43_node2
  · exact profile43_node3
  · exact profile43_node4

def profile43_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile43_node0 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [] 2 := by
  apply routed_branch (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [] 2 (by decide) (choices 4) [30] profile43_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [] (choices 4) [30] profile43_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node1

theorem profile43 : Upper (D (n:=5) [66,51,51,50,20]) (R (n:=5) [66,51,51,50,20]) [] 2 := profile43_node0

def profile44_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node1 : Upper (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [30] 2 (by decide) (choices 4) [] profile44_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [30] (choices 4) [] profile44_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile44_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile44_node0 : Upper (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [] 2 (by decide) (choices 4) [30] profile44_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [] (choices 4) [30] profile44_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node1

theorem profile44 : Upper (D (n:=5) [68,68,35,34,33]) (R (n:=5) [68,68,35,34,33]) [] 2 := profile44_node0

def profile45_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node1 : Upper (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [30] 2 (by decide) (choices 4) [] profile45_node1_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [30] (choices 4) [] profile45_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile45_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile45_node0 : Upper (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [] 2 (by decide) (choices 4) [30] profile45_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [] (choices 4) [30] profile45_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node1

theorem profile45 : Upper (D (n:=5) [68,67,36,34,33]) (R (n:=5) [68,67,36,34,33]) [] 2 := profile45_node0

def profile46_node2_cert : CutBound 5 := { lost := (rows 0 0 8 0 8), upper := (rows 31 15 7 15 23), lower := (rows 31 15 4 8 16), losses := [{ target := 3, region := (rows 1 2 7 0 19), good := (rows 23 23 4 0 16) }] }

theorem profile46_node2 : Upper (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30,13] 2 :=
  cut_bound_sound (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30,13] 2 profile46_node2_cert
    ((SmallCut.boundCheck_true (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30,13] 2 profile46_node2_cert).mp (by decide +kernel))

def profile46_node1_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node1 : Upper (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30] 2 := by
  apply routed_branch (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30] 2 (by decide) (choices 3) [13] profile46_node1_route
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [30] (choices 3) [13] profile46_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node2

def profile46_node0_route : Route 5 := (fun mask => (mask,id))

theorem profile46_node0 : Upper (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [] 2 := by
  apply routed_branch (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [] 2 (by decide) (choices 4) [30] profile46_node0_route
    (by change RowCover 5 4 (choices 4); exact cover ⟨4,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [] (choices 4) [30] profile46_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node1

theorem profile46 : Upper (D (n:=5) [68,52,51,34,33]) (R (n:=5) [68,52,51,34,33]) [] 2 := profile46_node0

#print axioms profile46
end Delivery.FiveVertexPositive14
