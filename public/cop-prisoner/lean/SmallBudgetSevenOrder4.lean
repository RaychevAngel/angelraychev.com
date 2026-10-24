import SmallRowPrefixBoolean
import SmallDegreeProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
4 vertices with seven arrows and total degree at least two at each vertex. -/
namespace Delivery.SmallBudgetSevenOrder4
open FiniteGame Extremal RowPrefix SmallDegreeProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d : Nat) : Rows 4 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | _ => d

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8]
  | 2 => [3,5,9,6,10,12]
  | 3 => [7,11,13,14]
  | 4 => [15]
  | _ => []

theorem cover (d : Fin 5) : RowCover 4 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile0_node0 : Upper (D (n:=4) [2,9,25,27]) (R (n:=4) [2,9,25,27]) [] 2 := by
  apply routed_branch (D (n:=4) [2,9,25,27]) (R (n:=4) [2,9,25,27]) [] 2 (by decide) (choices 0) [] profile0_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,9,25,27]) (R (n:=4) [2,9,25,27]) [] (choices 0) [] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile0 : Upper (D (n:=4) [2,9,25,27]) (R (n:=4) [2,9,25,27]) [] 2 := profile0_node0

def profile1_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile1_node1 : Upper (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [0] 2 (by decide) (choices 1) [] profile1_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [0] (choices 1) [] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile1_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile1_node0 : Upper (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [] 2 := by
  apply routed_branch (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [] 2 (by decide) (choices 0) [0] profile1_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [] (choices 0) [0] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=4) [2,9,26,26]) (R (n:=4) [2,9,26,26]) [] 2 := profile1_node0

def profile2_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile2_node0 : Upper (D (n:=4) [2,10,24,27]) (R (n:=4) [2,10,24,27]) [] 2 := by
  apply routed_branch (D (n:=4) [2,10,24,27]) (R (n:=4) [2,10,24,27]) [] 2 (by decide) (choices 0) [] profile2_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,10,24,27]) (R (n:=4) [2,10,24,27]) [] (choices 0) [] profile2_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile2 : Upper (D (n:=4) [2,10,24,27]) (R (n:=4) [2,10,24,27]) [] 2 := profile2_node0

def profile3_node3_cert : Bound 4 := { allowed := (rows 0 0 0 3), upper := (rows 1 10 15 15), lower := (rows 1 10 15 8), losses := [] }

theorem profile3_node3 : Upper (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8,11] 2 :=
  bound_sound (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8,11] 2 profile3_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8,11] 2 profile3_node3_cert).mp (by decide +kernel))

def profile3_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile3_node2 : Upper (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8] 2 := by
  apply routed_branch (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8] 2 (by decide) (choices 3) [11] profile3_node2_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0,8] (choices 3) [11] profile3_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node3

def profile3_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile3_node1 : Upper (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0] 2 (by decide) (choices 1) [8] profile3_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [0] (choices 1) [8] profile3_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node2

def profile3_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile3_node0 : Upper (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [] 2 := by
  apply routed_branch (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [] 2 (by decide) (choices 0) [0] profile3_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [] (choices 0) [0] profile3_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile3_node1

theorem profile3 : Upper (D (n:=4) [2,10,25,26]) (R (n:=4) [2,10,25,26]) [] 2 := profile3_node0

def profile4_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile4_node0 : Upper (D (n:=4) [2,11,24,26]) (R (n:=4) [2,11,24,26]) [] 2 := by
  apply routed_branch (D (n:=4) [2,11,24,26]) (R (n:=4) [2,11,24,26]) [] 2 (by decide) (choices 0) [] profile4_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,11,24,26]) (R (n:=4) [2,11,24,26]) [] (choices 0) [] profile4_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile4 : Upper (D (n:=4) [2,11,24,26]) (R (n:=4) [2,11,24,26]) [] 2 := profile4_node0

def profile5_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile5_node0 : Upper (D (n:=4) [2,11,25,25]) (R (n:=4) [2,11,25,25]) [] 2 := by
  apply routed_branch (D (n:=4) [2,11,25,25]) (R (n:=4) [2,11,25,25]) [] 2 (by decide) (choices 0) [] profile5_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,11,25,25]) (R (n:=4) [2,11,25,25]) [] (choices 0) [] profile5_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile5 : Upper (D (n:=4) [2,11,25,25]) (R (n:=4) [2,11,25,25]) [] 2 := profile5_node0

def profile6_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile6_node0 : Upper (D (n:=4) [2,16,18,27]) (R (n:=4) [2,16,18,27]) [] 2 := by
  apply routed_branch (D (n:=4) [2,16,18,27]) (R (n:=4) [2,16,18,27]) [] 2 (by decide) (choices 0) [] profile6_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,16,18,27]) (R (n:=4) [2,16,18,27]) [] (choices 0) [] profile6_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile6 : Upper (D (n:=4) [2,16,18,27]) (R (n:=4) [2,16,18,27]) [] 2 := profile6_node0

def profile7_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile7_node0 : Upper (D (n:=4) [2,16,19,26]) (R (n:=4) [2,16,19,26]) [] 2 := by
  apply routed_branch (D (n:=4) [2,16,19,26]) (R (n:=4) [2,16,19,26]) [] 2 (by decide) (choices 0) [] profile7_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,16,19,26]) (R (n:=4) [2,16,19,26]) [] (choices 0) [] profile7_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile7 : Upper (D (n:=4) [2,16,19,26]) (R (n:=4) [2,16,19,26]) [] 2 := profile7_node0

def profile8_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile8_node0 : Upper (D (n:=4) [2,17,17,27]) (R (n:=4) [2,17,17,27]) [] 2 := by
  apply routed_branch (D (n:=4) [2,17,17,27]) (R (n:=4) [2,17,17,27]) [] 2 (by decide) (choices 0) [] profile8_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,17,17,27]) (R (n:=4) [2,17,17,27]) [] (choices 0) [] profile8_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile8 : Upper (D (n:=4) [2,17,17,27]) (R (n:=4) [2,17,17,27]) [] 2 := profile8_node0

def profile9_node3_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 1 14 13 15), lower := (rows 1 14 13 8), losses := [{ target := 0, region := (rows 0 6 4 8), good := (rows 0 14 14 8) }] }

theorem profile9_node3 : Upper (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12,9] 2 :=
  bound_sound (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12,9] 2 profile9_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12,9] 2 profile9_node3_cert).mp (by decide +kernel))

def profile9_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile9_node2 : Upper (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12] 2 := by
  apply routed_branch (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12] 2 (by decide) (choices 2) [9] profile9_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0,12] (choices 2) [9] profile9_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node3

def profile9_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile9_node1 : Upper (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0] 2 (by decide) (choices 2) [12] profile9_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [0] (choices 2) [12] profile9_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node2

def profile9_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile9_node0 : Upper (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [] 2 := by
  apply routed_branch (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [] 2 (by decide) (choices 0) [0] profile9_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [] (choices 0) [0] profile9_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node1

theorem profile9 : Upper (D (n:=4) [2,17,18,26]) (R (n:=4) [2,17,18,26]) [] 2 := profile9_node0

def profile10_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile10_node0 : Upper (D (n:=4) [2,17,19,25]) (R (n:=4) [2,17,19,25]) [] 2 := by
  apply routed_branch (D (n:=4) [2,17,19,25]) (R (n:=4) [2,17,19,25]) [] 2 (by decide) (choices 0) [] profile10_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,17,19,25]) (R (n:=4) [2,17,19,25]) [] (choices 0) [] profile10_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile10 : Upper (D (n:=4) [2,17,19,25]) (R (n:=4) [2,17,19,25]) [] 2 := profile10_node0

def profile11_node4_cert : Bound 4 := { allowed := (rows 0 0 1 0), upper := (rows 1 7 14 15), lower := (rows 1 7 14 15), losses := [] }

theorem profile11_node4 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10,7] 2 :=
  bound_sound (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10,7] 2 profile11_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10,7] 2 profile11_node4_cert).mp (by decide +kernel))

def profile11_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node3 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10] 2 (by decide) (choices 3) [7] profile11_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5,10] (choices 3) [7] profile11_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node4

def profile11_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node2 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5] 2 (by decide) (choices 2) [10] profile11_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,5] (choices 2) [10] profile11_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node3

def profile11_node7_cert : Bound 4 := { allowed := (rows 0 1 0 0), upper := (rows 1 14 7 15), lower := (rows 1 14 7 15), losses := [] }

theorem profile11_node7 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3,7] 2 :=
  bound_sound (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3,7] 2 profile11_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3,7] 2 profile11_node7_cert).mp (by decide +kernel))

def profile11_node6_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node6 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3] 2 (by decide) (choices 3) [7] profile11_node6_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12,3] (choices 3) [7] profile11_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node7

def profile11_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node5 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12] 2 (by decide) (choices 2) [3] profile11_node5_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0,12] (choices 2) [3] profile11_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node6

def profile11_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node1 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0] 2 (by decide) (choices 2) [5,12] profile11_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [0] (choices 2) [5,12] profile11_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node2
  · exact profile11_node5

def profile11_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile11_node0 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [] 2 := by
  apply routed_branch (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [] 2 (by decide) (choices 0) [0] profile11_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [] (choices 0) [0] profile11_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile11_node1

theorem profile11 : Upper (D (n:=4) [2,18,18,25]) (R (n:=4) [2,18,18,25]) [] 2 := profile11_node0

def profile12_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile12_node0 : Upper (D (n:=4) [2,18,19,24]) (R (n:=4) [2,18,19,24]) [] 2 := by
  apply routed_branch (D (n:=4) [2,18,19,24]) (R (n:=4) [2,18,19,24]) [] 2 (by decide) (choices 0) [] profile12_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [2,18,19,24]) (R (n:=4) [2,18,19,24]) [] (choices 0) [] profile12_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile12 : Upper (D (n:=4) [2,18,19,24]) (R (n:=4) [2,18,19,24]) [] 2 := profile12_node0

def profile13_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile13_node0 : Upper (D (n:=4) [3,9,24,27]) (R (n:=4) [3,9,24,27]) [] 2 := by
  apply routed_branch (D (n:=4) [3,9,24,27]) (R (n:=4) [3,9,24,27]) [] 2 (by decide) (choices 0) [] profile13_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,9,24,27]) (R (n:=4) [3,9,24,27]) [] (choices 0) [] profile13_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile13 : Upper (D (n:=4) [3,9,24,27]) (R (n:=4) [3,9,24,27]) [] 2 := profile13_node0

def profile14_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [0] 2 (by decide) (choices 1) [] profile14_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [0] (choices 1) [] profile14_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile14_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile14_node0 : Upper (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [] 2 := by
  apply routed_branch (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [] 2 (by decide) (choices 0) [0] profile14_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [] (choices 0) [0] profile14_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node1

theorem profile14 : Upper (D (n:=4) [3,9,25,26]) (R (n:=4) [3,9,25,26]) [] 2 := profile14_node0

def profile15_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [0] 2 (by decide) (choices 1) [] profile15_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [0] (choices 1) [] profile15_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile15_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile15_node0 : Upper (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [] 2 := by
  apply routed_branch (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [] 2 (by decide) (choices 0) [0] profile15_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [] (choices 0) [0] profile15_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile15_node1

theorem profile15 : Upper (D (n:=4) [3,10,24,26]) (R (n:=4) [3,10,24,26]) [] 2 := profile15_node0

def profile16_node3_cert : Bound 4 := { allowed := (rows 0 0 0 3), upper := (rows 1 3 15 15), lower := (rows 1 3 15 8), losses := [] }

theorem profile16_node3 : Upper (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1,11] 2 :=
  bound_sound (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1,11] 2 profile16_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1,11] 2 profile16_node3_cert).mp (by decide +kernel))

def profile16_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile16_node2 : Upper (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1] 2 := by
  apply routed_branch (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1] 2 (by decide) (choices 3) [11] profile16_node2_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0,1] (choices 3) [11] profile16_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node3

def profile16_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile16_node1 : Upper (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0] 2 (by decide) (choices 1) [1] profile16_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [0] (choices 1) [1] profile16_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node2

def profile16_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile16_node0 : Upper (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [] 2 := by
  apply routed_branch (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [] 2 (by decide) (choices 0) [0] profile16_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [] (choices 0) [0] profile16_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node1

theorem profile16 : Upper (D (n:=4) [3,10,25,25]) (R (n:=4) [3,10,25,25]) [] 2 := profile16_node0

def profile17_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile17_node0 : Upper (D (n:=4) [3,11,24,25]) (R (n:=4) [3,11,24,25]) [] 2 := by
  apply routed_branch (D (n:=4) [3,11,24,25]) (R (n:=4) [3,11,24,25]) [] 2 (by decide) (choices 0) [] profile17_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,11,24,25]) (R (n:=4) [3,11,24,25]) [] (choices 0) [] profile17_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile17 : Upper (D (n:=4) [3,11,24,25]) (R (n:=4) [3,11,24,25]) [] 2 := profile17_node0

def profile18_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile18_node0 : Upper (D (n:=4) [3,16,17,27]) (R (n:=4) [3,16,17,27]) [] 2 := by
  apply routed_branch (D (n:=4) [3,16,17,27]) (R (n:=4) [3,16,17,27]) [] 2 (by decide) (choices 0) [] profile18_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,16,17,27]) (R (n:=4) [3,16,17,27]) [] (choices 0) [] profile18_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile18 : Upper (D (n:=4) [3,16,17,27]) (R (n:=4) [3,16,17,27]) [] 2 := profile18_node0

def profile19_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile19_node1 : Upper (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [0] 2 (by decide) (choices 2) [] profile19_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [0] (choices 2) [] profile19_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile19_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile19_node0 : Upper (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [] 2 := by
  apply routed_branch (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [] 2 (by decide) (choices 0) [0] profile19_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [] (choices 0) [0] profile19_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile19_node1

theorem profile19 : Upper (D (n:=4) [3,16,18,26]) (R (n:=4) [3,16,18,26]) [] 2 := profile19_node0

def profile20_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile20_node0 : Upper (D (n:=4) [3,16,19,25]) (R (n:=4) [3,16,19,25]) [] 2 := by
  apply routed_branch (D (n:=4) [3,16,19,25]) (R (n:=4) [3,16,19,25]) [] 2 (by decide) (choices 0) [] profile20_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,16,19,25]) (R (n:=4) [3,16,19,25]) [] (choices 0) [] profile20_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile20 : Upper (D (n:=4) [3,16,19,25]) (R (n:=4) [3,16,19,25]) [] 2 := profile20_node0

def profile21_node3_cert : Bound 4 := { allowed := (rows 0 0 0 1), upper := (rows 1 11 13 15), lower := (rows 1 11 13 8), losses := [] }

theorem profile21_node3 : Upper (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9,9] 2 :=
  bound_sound (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9,9] 2 profile21_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9,9] 2 profile21_node3_cert).mp (by decide +kernel))

def profile21_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile21_node2 : Upper (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9] 2 := by
  apply routed_branch (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9] 2 (by decide) (choices 2) [9] profile21_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0,9] (choices 2) [9] profile21_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node3

def profile21_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile21_node1 : Upper (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0] 2 (by decide) (choices 2) [9] profile21_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [0] (choices 2) [9] profile21_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node2

def profile21_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile21_node0 : Upper (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [] 2 := by
  apply routed_branch (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [] 2 (by decide) (choices 0) [0] profile21_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [] (choices 0) [0] profile21_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile21_node1

theorem profile21 : Upper (D (n:=4) [3,17,17,26]) (R (n:=4) [3,17,17,26]) [] 2 := profile21_node0

def profile22_node3_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 1 7 13 15), lower := (rows 1 7 13 8), losses := [] }

theorem profile22_node3 : Upper (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5,9] 2 :=
  bound_sound (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5,9] 2 profile22_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5,9] 2 profile22_node3_cert).mp (by decide +kernel))

def profile22_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile22_node2 : Upper (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5] 2 := by
  apply routed_branch (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5] 2 (by decide) (choices 2) [9] profile22_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0,5] (choices 2) [9] profile22_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node3

def profile22_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile22_node1 : Upper (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0] 2 (by decide) (choices 2) [5] profile22_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [0] (choices 2) [5] profile22_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node2

def profile22_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile22_node0 : Upper (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [] 2 := by
  apply routed_branch (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [] 2 (by decide) (choices 0) [0] profile22_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [] (choices 0) [0] profile22_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile22_node1

theorem profile22 : Upper (D (n:=4) [3,17,18,25]) (R (n:=4) [3,17,18,25]) [] 2 := profile22_node0

def profile23_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile23_node0 : Upper (D (n:=4) [3,17,19,24]) (R (n:=4) [3,17,19,24]) [] 2 := by
  apply routed_branch (D (n:=4) [3,17,19,24]) (R (n:=4) [3,17,19,24]) [] 2 (by decide) (choices 0) [] profile23_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,17,19,24]) (R (n:=4) [3,17,19,24]) [] (choices 0) [] profile23_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile23 : Upper (D (n:=4) [3,17,19,24]) (R (n:=4) [3,17,19,24]) [] 2 := profile23_node0

def profile24_node4_cert : Bound 4 := { allowed := (rows 0 0 0 0), upper := (rows 1 7 7 15), lower := (rows 1 7 7 15), losses := [] }

theorem profile24_node4 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3,7] 2 :=
  bound_sound (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3,7] 2 profile24_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3,7] 2 profile24_node4_cert).mp (by decide +kernel))

def profile24_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile24_node3 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3] 2 := by
  apply routed_branch (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3] 2 (by decide) (choices 3) [7] profile24_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5,3] (choices 3) [7] profile24_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node4

def profile24_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile24_node2 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5] 2 := by
  apply routed_branch (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5] 2 (by decide) (choices 2) [3] profile24_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0,5] (choices 2) [3] profile24_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node3

def profile24_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile24_node1 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0] 2 := by
  apply routed_branch (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0] 2 (by decide) (choices 2) [5] profile24_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [0] (choices 2) [5] profile24_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node2

def profile24_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile24_node0 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [] 2 := by
  apply routed_branch (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [] 2 (by decide) (choices 0) [0] profile24_node0_route
    (by change RowCover 4 0 (choices 0); exact cover ⟨0,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [] (choices 0) [0] profile24_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile24_node1

theorem profile24 : Upper (D (n:=4) [3,18,18,24]) (R (n:=4) [3,18,18,24]) [] 2 := profile24_node0

def profile25_node0_cert : Bound 4 := { allowed := (rows 0 0 8 4), upper := (rows 15 15 15 15), lower := (rows 1 2 4 8), losses := [] }

theorem profile25_node0 : Upper (D (n:=4) [9,9,18,27]) (R (n:=4) [9,9,18,27]) [] 2 :=
  bound_sound (D (n:=4) [9,9,18,27]) (R (n:=4) [9,9,18,27]) [] 2 profile25_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,9,18,27]) (R (n:=4) [9,9,18,27]) [] 2 profile25_node0_cert).mp (by decide +kernel))

theorem profile25 : Upper (D (n:=4) [9,9,18,27]) (R (n:=4) [9,9,18,27]) [] 2 := profile25_node0

def profile26_node0_cert : Bound 4 := { allowed := (rows 0 0 8 4), upper := (rows 15 15 15 15), lower := (rows 1 2 4 8), losses := [] }

theorem profile26_node0 : Upper (D (n:=4) [9,9,19,26]) (R (n:=4) [9,9,19,26]) [] 2 :=
  bound_sound (D (n:=4) [9,9,19,26]) (R (n:=4) [9,9,19,26]) [] 2 profile26_node0_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,9,19,26]) (R (n:=4) [9,9,19,26]) [] 2 profile26_node0_cert).mp (by decide +kernel))

theorem profile26 : Upper (D (n:=4) [9,9,19,26]) (R (n:=4) [9,9,19,26]) [] 2 := profile26_node0

def profile27_node3_cert : Bound 4 := { allowed := (rows 0 0 0 2), upper := (rows 9 10 14 15), lower := (rows 9 10 14 8), losses := [] }

theorem profile27_node3 : Upper (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8,10] 2 :=
  bound_sound (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8,10] 2 profile27_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8,10] 2 profile27_node3_cert).mp (by decide +kernel))

def profile27_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile27_node2 : Upper (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8] 2 := by
  apply routed_branch (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8] 2 (by decide) (choices 2) [10] profile27_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8,8] (choices 2) [10] profile27_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node3

def profile27_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile27_node1 : Upper (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8] 2 := by
  apply routed_branch (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8] 2 (by decide) (choices 1) [8] profile27_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [8] (choices 1) [8] profile27_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node2

def profile27_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile27_node0 : Upper (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [] 2 := by
  apply routed_branch (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [] 2 (by decide) (choices 1) [8] profile27_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [] (choices 1) [8] profile27_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile27_node1

theorem profile27 : Upper (D (n:=4) [9,10,17,27]) (R (n:=4) [9,10,17,27]) [] 2 := profile27_node0

def profile28_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node1 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [2] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [2] 2 (by decide) (choices 1) [] profile28_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [2] (choices 1) [] profile28_node1_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile28_node4_cert : Bound 4 := { allowed := (rows 0 0 0 6), upper := (rows 5 10 14 15), lower := (rows 5 10 14 8), losses := [] }

theorem profile28_node4 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8,10] 2 :=
  bound_sound (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8,10] 2 profile28_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8,10] 2 profile28_node4_cert).mp (by decide +kernel))

def profile28_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node3 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8] 2 (by decide) (choices 2) [10] profile28_node3_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4,8] (choices 2) [10] profile28_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node4

def profile28_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node2 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4] 2 (by decide) (choices 1) [8] profile28_node2_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [4] (choices 1) [8] profile28_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node3

def profile28_node7_cert : Bound 4 := { allowed := (rows 0 0 0 6), upper := (rows 9 6 14 15), lower := (rows 9 6 14 8), losses := [] }

theorem profile28_node7 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4,10] 2 :=
  bound_sound (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4,10] 2 profile28_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4,10] 2 profile28_node7_cert).mp (by decide +kernel))

def profile28_node6_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node6 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4] 2 (by decide) (choices 2) [10] profile28_node6_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8,4] (choices 2) [10] profile28_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node7

def profile28_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node5 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8] 2 (by decide) (choices 1) [4] profile28_node5_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [8] (choices 1) [4] profile28_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile28_node6

def profile28_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile28_node0 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [] 2 := by
  apply routed_branch (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [] 2 (by decide) (choices 1) [2,4,8] profile28_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [] (choices 1) [2,4,8] profile28_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile28_node1
  · exact profile28_node2
  · exact profile28_node5

theorem profile28 : Upper (D (n:=4) [9,10,18,26]) (R (n:=4) [9,10,18,26]) [] 2 := profile28_node0

def profile29_node3_cert : Bound 4 := { allowed := (rows 0 0 0 6), upper := (rows 5 6 14 15), lower := (rows 5 6 14 8), losses := [] }

theorem profile29_node3 : Upper (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4,10] 2 :=
  bound_sound (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4,10] 2 profile29_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4,10] 2 profile29_node3_cert).mp (by decide +kernel))

def profile29_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile29_node2 : Upper (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4] 2 := by
  apply routed_branch (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4] 2 (by decide) (choices 2) [10] profile29_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4,4] (choices 2) [10] profile29_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node3

def profile29_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile29_node1 : Upper (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4] 2 := by
  apply routed_branch (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4] 2 (by decide) (choices 1) [4] profile29_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [4] (choices 1) [4] profile29_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node2

def profile29_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile29_node0 : Upper (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [] 2 := by
  apply routed_branch (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [] 2 (by decide) (choices 1) [4] profile29_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [] (choices 1) [4] profile29_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node1

theorem profile29 : Upper (D (n:=4) [9,10,19,25]) (R (n:=4) [9,10,19,25]) [] 2 := profile29_node0

def profile30_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile30_node0 : Upper (D (n:=4) [9,11,16,27]) (R (n:=4) [9,11,16,27]) [] 2 := by
  apply routed_branch (D (n:=4) [9,11,16,27]) (R (n:=4) [9,11,16,27]) [] 2 (by decide) (choices 1) [] profile30_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,16,27]) (R (n:=4) [9,11,16,27]) [] (choices 1) [] profile30_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile30 : Upper (D (n:=4) [9,11,16,27]) (R (n:=4) [9,11,16,27]) [] 2 := profile30_node0

def profile31_node3_cert : Bound 4 := { allowed := (rows 0 0 0 2), upper := (rows 3 10 14 15), lower := (rows 3 10 14 8), losses := [] }

theorem profile31_node3 : Upper (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8,10] 2 :=
  bound_sound (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8,10] 2 profile31_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8,10] 2 profile31_node3_cert).mp (by decide +kernel))

def profile31_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile31_node2 : Upper (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8] 2 := by
  apply routed_branch (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8] 2 (by decide) (choices 2) [10] profile31_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2,8] (choices 2) [10] profile31_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile31_node3

def profile31_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile31_node1 : Upper (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2] 2 := by
  apply routed_branch (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2] 2 (by decide) (choices 1) [8] profile31_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [2] (choices 1) [8] profile31_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile31_node2

def profile31_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile31_node0 : Upper (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [] 2 := by
  apply routed_branch (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [] 2 (by decide) (choices 1) [2] profile31_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [] (choices 1) [2] profile31_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile31_node1

theorem profile31 : Upper (D (n:=4) [9,11,17,26]) (R (n:=4) [9,11,17,26]) [] 2 := profile31_node0

def profile32_node3_cert : Bound 4 := { allowed := (rows 0 0 0 6), upper := (rows 3 6 14 15), lower := (rows 3 6 14 8), losses := [] }

theorem profile32_node3 : Upper (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4,10] 2 :=
  bound_sound (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4,10] 2 profile32_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4,10] 2 profile32_node3_cert).mp (by decide +kernel))

def profile32_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile32_node2 : Upper (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4] 2 := by
  apply routed_branch (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4] 2 (by decide) (choices 2) [10] profile32_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2,4] (choices 2) [10] profile32_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node3

def profile32_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile32_node1 : Upper (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2] 2 := by
  apply routed_branch (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2] 2 (by decide) (choices 1) [4] profile32_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [2] (choices 1) [4] profile32_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node2

def profile32_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile32_node0 : Upper (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [] 2 := by
  apply routed_branch (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [] 2 (by decide) (choices 1) [2] profile32_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [] (choices 1) [2] profile32_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile32_node1

theorem profile32 : Upper (D (n:=4) [9,11,18,25]) (R (n:=4) [9,11,18,25]) [] 2 := profile32_node0

def profile33_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile33_node0 : Upper (D (n:=4) [9,11,19,24]) (R (n:=4) [9,11,19,24]) [] 2 := by
  apply routed_branch (D (n:=4) [9,11,19,24]) (R (n:=4) [9,11,19,24]) [] 2 (by decide) (choices 1) [] profile33_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,11,19,24]) (R (n:=4) [9,11,19,24]) [] (choices 1) [] profile33_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile33 : Upper (D (n:=4) [9,11,19,24]) (R (n:=4) [9,11,19,24]) [] 2 := profile33_node0

def profile34_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile34_node0 : Upper (D (n:=4) [9,16,19,19]) (R (n:=4) [9,16,19,19]) [] 2 := by
  apply routed_branch (D (n:=4) [9,16,19,19]) (R (n:=4) [9,16,19,19]) [] 2 (by decide) (choices 1) [] profile34_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,16,19,19]) (R (n:=4) [9,16,19,19]) [] (choices 1) [] profile34_node0_route).mp (by decide +kernel))
  intro mask member
  simp at member

theorem profile34 : Upper (D (n:=4) [9,16,19,19]) (R (n:=4) [9,16,19,19]) [] 2 := profile34_node0

def profile35_node2_cert : Bound 4 := { allowed := (rows 0 0 8 4), upper := (rows 9 14 15 15), lower := (rows 9 14 4 8), losses := [] }

theorem profile35_node2 : Upper (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8,12] 2 :=
  bound_sound (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8,12] 2 profile35_node2_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8,12] 2 profile35_node2_cert).mp (by decide +kernel))

def profile35_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile35_node1 : Upper (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8] 2 := by
  apply routed_branch (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8] 2 (by decide) (choices 2) [12] profile35_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [8] (choices 2) [12] profile35_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node2

def profile35_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile35_node0 : Upper (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [] 2 := by
  apply routed_branch (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [] 2 (by decide) (choices 1) [8] profile35_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [] (choices 1) [8] profile35_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile35_node1

theorem profile35 : Upper (D (n:=4) [9,17,18,19]) (R (n:=4) [9,17,18,19]) [] 2 := profile35_node0

def profile36_node4_cert : Bound 4 := { allowed := (rows 0 0 2 0), upper := (rows 3 14 13 14), lower := (rows 3 14 13 14), losses := [] }

theorem profile36_node4 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9,6] 2 :=
  bound_sound (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9,6] 2 profile36_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9,6] 2 profile36_node4_cert).mp (by decide +kernel))

def profile36_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile36_node3 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9] 2 := by
  apply routed_branch (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9] 2 (by decide) (choices 2) [6] profile36_node3_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,9] (choices 2) [6] profile36_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node4

def profile36_node5_cert : Bound 4 := { allowed := (rows 0 0 0 6), upper := (rows 3 14 14 13), lower := (rows 3 14 14 8), losses := [] }

theorem profile36_node5 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,10] 2 :=
  bound_sound (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,10] 2 profile36_node5_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12,10] 2 profile36_node5_cert).mp (by decide +kernel))

def profile36_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile36_node2 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12] 2 := by
  apply routed_branch (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12] 2 (by decide) (choices 2) [9,10] profile36_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2,12] (choices 2) [9,10] profile36_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile36_node3
  · exact profile36_node5

def profile36_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile36_node1 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2] 2 := by
  apply routed_branch (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2] 2 (by decide) (choices 2) [12] profile36_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [2] (choices 2) [12] profile36_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node2

def profile36_node0_route : Route 4 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 8 => (2,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile36_node0 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [] 2 := by
  apply routed_branch (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [] 2 (by decide) (choices 1) [2] profile36_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [] (choices 1) [2] profile36_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile36_node1

theorem profile36 : Upper (D (n:=4) [9,18,18,18]) (R (n:=4) [9,18,18,18]) [] 2 := profile36_node0

def profile37_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile37_node2 : Upper (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8,8] 2 := by
  apply routed_branch (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8,8] 2 (by decide) (choices 2) [] profile37_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8,8] (choices 2) [] profile37_node2_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile37_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile37_node1 : Upper (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8] 2 := by
  apply routed_branch (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8] 2 (by decide) (choices 1) [8] profile37_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [8] (choices 1) [8] profile37_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node2

def profile37_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile37_node0 : Upper (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [] 2 := by
  apply routed_branch (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [] 2 (by decide) (choices 1) [8] profile37_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [] (choices 1) [8] profile37_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile37_node1

theorem profile37 : Upper (D (n:=4) [10,10,16,27]) (R (n:=4) [10,10,16,27]) [] 2 := profile37_node0

def profile38_node4_cert : Bound 4 := { allowed := (rows 0 0 2 0), upper := (rows 3 10 13 15), lower := (rows 3 10 13 15), losses := [] }

theorem profile38_node4 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9,7] 2 :=
  bound_sound (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9,7] 2 profile38_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9,7] 2 profile38_node4_cert).mp (by decide +kernel))

def profile38_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node3 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9] 2 (by decide) (choices 3) [7] profile38_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8,9] (choices 3) [7] profile38_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node4

def profile38_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node2 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8] 2 (by decide) (choices 2) [9] profile38_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2,8] (choices 2) [9] profile38_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node3

def profile38_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node1 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2] 2 (by decide) (choices 1) [8] profile38_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [2] (choices 1) [8] profile38_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node2

def profile38_node6_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node6 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4,8] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4,8] 2 (by decide) (choices 2) [] profile38_node6_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4,8] (choices 2) [] profile38_node6_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile38_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node5 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4] 2 (by decide) (choices 1) [8] profile38_node5_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [4] (choices 1) [8] profile38_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node6

def profile38_node10_cert : Bound 4 := { allowed := (rows 0 0 1 0), upper := (rows 9 3 14 15), lower := (rows 9 3 14 15), losses := [] }

theorem profile38_node10 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10,7] 2 :=
  bound_sound (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10,7] 2 profile38_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10,7] 2 profile38_node10_cert).mp (by decide +kernel))

def profile38_node9_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node9 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10] 2 (by decide) (choices 3) [7] profile38_node9_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1,10] (choices 3) [7] profile38_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node10

def profile38_node8_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node8 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1] 2 (by decide) (choices 2) [10] profile38_node8_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,1] (choices 2) [10] profile38_node8_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node9

def profile38_node11_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node11 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,4] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,4] 2 (by decide) (choices 2) [] profile38_node11_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,4] (choices 2) [] profile38_node11_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile38_node14_cert : Bound 4 := { allowed := (rows 0 0 8 0), upper := (rows 9 10 7 15), lower := (rows 9 10 7 15), losses := [] }

theorem profile38_node14 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3,7] 2 :=
  bound_sound (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3,7] 2 profile38_node14_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3,7] 2 profile38_node14_cert).mp (by decide +kernel))

def profile38_node13_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node13 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3] 2 (by decide) (choices 3) [7] profile38_node13_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8,3] (choices 3) [7] profile38_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node14

def profile38_node12_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node12 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8] 2 (by decide) (choices 2) [3] profile38_node12_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8,8] (choices 2) [3] profile38_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile38_node13

def profile38_node7_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node7 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8] 2 (by decide) (choices 1) [1,4,8] profile38_node7_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [8] (choices 1) [1,4,8] profile38_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node8
  · exact profile38_node11
  · exact profile38_node12

def profile38_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile38_node0 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [] 2 := by
  apply routed_branch (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [] 2 (by decide) (choices 1) [2,4,8] profile38_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [] (choices 1) [2,4,8] profile38_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile38_node1
  · exact profile38_node5
  · exact profile38_node7

theorem profile38 : Upper (D (n:=4) [10,10,17,26]) (R (n:=4) [10,10,17,26]) [] 2 := profile38_node0

def profile39_node4_cert : Bound 4 := { allowed := (rows 0 0 2 0), upper := (rows 3 6 13 15), lower := (rows 3 6 13 15), losses := [] }

theorem profile39_node4 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9,7] 2 :=
  bound_sound (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9,7] 2 profile39_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9,7] 2 profile39_node4_cert).mp (by decide +kernel))

def profile39_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node3 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9] 2 (by decide) (choices 3) [7] profile39_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4,9] (choices 3) [7] profile39_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node4

def profile39_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node2 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4] 2 (by decide) (choices 2) [9] profile39_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2,4] (choices 2) [9] profile39_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node3

def profile39_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node1 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2] 2 (by decide) (choices 1) [4] profile39_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [2] (choices 1) [4] profile39_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node2

def profile39_node8_cert : Bound 4 := { allowed := (rows 0 0 1 0), upper := (rows 5 3 14 15), lower := (rows 5 3 14 15), losses := [] }

theorem profile39_node8 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10,7] 2 :=
  bound_sound (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10,7] 2 profile39_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10,7] 2 profile39_node8_cert).mp (by decide +kernel))

def profile39_node7_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node7 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10] 2 (by decide) (choices 3) [7] profile39_node7_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1,10] (choices 3) [7] profile39_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node8

def profile39_node6_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node6 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1] 2 (by decide) (choices 2) [10] profile39_node6_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,1] (choices 2) [10] profile39_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node7

def profile39_node9_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node9 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,4] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,4] 2 (by decide) (choices 2) [] profile39_node9_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,4] (choices 2) [] profile39_node9_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile39_node12_cert : Bound 4 := { allowed := (rows 0 0 0 0), upper := (rows 5 10 7 15), lower := (rows 5 10 7 15), losses := [] }

theorem profile39_node12 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3,7] 2 :=
  bound_sound (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3,7] 2 profile39_node12_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3,7] 2 profile39_node12_cert).mp (by decide +kernel))

def profile39_node11_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node11 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3] 2 (by decide) (choices 3) [7] profile39_node11_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8,3] (choices 3) [7] profile39_node11_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node12

def profile39_node10_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node10 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8] 2 (by decide) (choices 2) [3] profile39_node10_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4,8] (choices 2) [3] profile39_node10_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node11

def profile39_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node5 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4] 2 (by decide) (choices 1) [1,4,8] profile39_node5_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [4] (choices 1) [1,4,8] profile39_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile39_node6
  · exact profile39_node9
  · exact profile39_node10

def profile39_node16_cert : Bound 4 := { allowed := (rows 0 0 0 0), upper := (rows 9 6 7 15), lower := (rows 9 6 7 15), losses := [] }

theorem profile39_node16 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3,7] 2 :=
  bound_sound (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3,7] 2 profile39_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3,7] 2 profile39_node16_cert).mp (by decide +kernel))

def profile39_node15_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node15 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3] 2 (by decide) (choices 3) [7] profile39_node15_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4,3] (choices 3) [7] profile39_node15_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node16

def profile39_node14_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node14 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4] 2 (by decide) (choices 2) [3] profile39_node14_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8,4] (choices 2) [3] profile39_node14_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node15

def profile39_node13_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node13 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8] 2 (by decide) (choices 1) [4] profile39_node13_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [8] (choices 1) [4] profile39_node13_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile39_node14

def profile39_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile39_node0 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [] 2 := by
  apply routed_branch (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [] 2 (by decide) (choices 1) [2,4,8] profile39_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [] (choices 1) [2,4,8] profile39_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile39_node1
  · exact profile39_node5
  · exact profile39_node13

theorem profile39 : Upper (D (n:=4) [10,10,18,25]) (R (n:=4) [10,10,18,25]) [] 2 := profile39_node0

def profile40_node4_cert : Bound 4 := { allowed := (rows 0 0 0 0), upper := (rows 5 6 7 15), lower := (rows 5 6 7 15), losses := [] }

theorem profile40_node4 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3,7] 2 :=
  bound_sound (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3,7] 2 profile40_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3,7] 2 profile40_node4_cert).mp (by decide +kernel))

def profile40_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile40_node3 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3] 2 := by
  apply routed_branch (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3] 2 (by decide) (choices 3) [7] profile40_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4,3] (choices 3) [7] profile40_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node4

def profile40_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile40_node2 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4] 2 := by
  apply routed_branch (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4] 2 (by decide) (choices 2) [3] profile40_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4,4] (choices 2) [3] profile40_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node3

def profile40_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile40_node1 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4] 2 := by
  apply routed_branch (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4] 2 (by decide) (choices 1) [4] profile40_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [4] (choices 1) [4] profile40_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node2

def profile40_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile40_node0 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [] 2 := by
  apply routed_branch (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [] 2 (by decide) (choices 1) [4] profile40_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [] (choices 1) [4] profile40_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile40_node1

theorem profile40 : Upper (D (n:=4) [10,10,19,24]) (R (n:=4) [10,10,19,24]) [] 2 := profile40_node0

def profile41_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile41_node2 : Upper (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2,8] 2 := by
  apply routed_branch (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2,8] 2 (by decide) (choices 2) [] profile41_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2,8] (choices 2) [] profile41_node2_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile41_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile41_node1 : Upper (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2] 2 (by decide) (choices 1) [8] profile41_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [2] (choices 1) [8] profile41_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node2

def profile41_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile41_node0 : Upper (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [] 2 := by
  apply routed_branch (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [] 2 (by decide) (choices 1) [2] profile41_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [] (choices 1) [2] profile41_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node1

theorem profile41 : Upper (D (n:=4) [10,11,16,26]) (R (n:=4) [10,11,16,26]) [] 2 := profile41_node0

def profile42_node4_cert : Bound 4 := { allowed := (rows 0 0 1 0), upper := (rows 3 3 14 15), lower := (rows 3 3 14 15), losses := [] }

theorem profile42_node4 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10,7] 2 :=
  bound_sound (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10,7] 2 profile42_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10,7] 2 profile42_node4_cert).mp (by decide +kernel))

def profile42_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node3 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10] 2 (by decide) (choices 3) [7] profile42_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1,10] (choices 3) [7] profile42_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node4

def profile42_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node2 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1] 2 (by decide) (choices 2) [10] profile42_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,1] (choices 2) [10] profile42_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node3

def profile42_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node5 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,4] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,4] 2 (by decide) (choices 2) [] profile42_node5_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,4] (choices 2) [] profile42_node5_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile42_node7_cert : Bound 4 := { allowed := (rows 0 0 0 3), upper := (rows 3 10 7 15), lower := (rows 3 10 7 8), losses := [] }

theorem profile42_node7 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8,3] 2 :=
  bound_sound (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8,3] 2 profile42_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8,3] 2 profile42_node7_cert).mp (by decide +kernel))

def profile42_node6_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node6 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8] 2 (by decide) (choices 2) [3] profile42_node6_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2,8] (choices 2) [3] profile42_node6_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node7

def profile42_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node1 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2] 2 (by decide) (choices 1) [1,4,8] profile42_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [2] (choices 1) [1,4,8] profile42_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile42_node2
  · exact profile42_node5
  · exact profile42_node6

def profile42_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile42_node0 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [] 2 := by
  apply routed_branch (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [] 2 (by decide) (choices 1) [2] profile42_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [] (choices 1) [2] profile42_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile42_node1

theorem profile42 : Upper (D (n:=4) [10,11,17,25]) (R (n:=4) [10,11,17,25]) [] 2 := profile42_node0

def profile43_node4_cert : Bound 4 := { allowed := (rows 0 0 0 0), upper := (rows 3 6 7 15), lower := (rows 3 6 7 15), losses := [] }

theorem profile43_node4 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3,7] 2 :=
  bound_sound (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3,7] 2 profile43_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3,7] 2 profile43_node4_cert).mp (by decide +kernel))

def profile43_node3_route : Route 4 := (fun mask => (mask,id))

theorem profile43_node3 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3] 2 := by
  apply routed_branch (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3] 2 (by decide) (choices 3) [7] profile43_node3_route
    (by change RowCover 4 3 (choices 3); exact cover ⟨3,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4,3] (choices 3) [7] profile43_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node4

def profile43_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile43_node2 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4] 2 := by
  apply routed_branch (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4] 2 (by decide) (choices 2) [3] profile43_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2,4] (choices 2) [3] profile43_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node3

def profile43_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile43_node1 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2] 2 (by decide) (choices 1) [4] profile43_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [2] (choices 1) [4] profile43_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node2

def profile43_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile43_node0 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [] 2 := by
  apply routed_branch (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [] 2 (by decide) (choices 1) [2] profile43_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [] (choices 1) [2] profile43_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile43_node1

theorem profile43 : Upper (D (n:=4) [10,11,18,24]) (R (n:=4) [10,11,18,24]) [] 2 := profile43_node0

def profile44_node3_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 9 14 13 13), lower := (rows 9 14 13 8), losses := [{ target := 0, region := (rows 0 6 4 8), good := (rows 8 14 14 8) }] }

theorem profile44_node3 : Upper (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12,9] 2 :=
  bound_sound (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12,9] 2 profile44_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12,9] 2 profile44_node3_cert).mp (by decide +kernel))

def profile44_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile44_node2 : Upper (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12] 2 := by
  apply routed_branch (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12] 2 (by decide) (choices 2) [9] profile44_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8,12] (choices 2) [9] profile44_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node3

def profile44_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile44_node1 : Upper (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8] 2 := by
  apply routed_branch (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8] 2 (by decide) (choices 2) [12] profile44_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [8] (choices 2) [12] profile44_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node2

def profile44_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile44_node0 : Upper (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [] 2 := by
  apply routed_branch (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [] 2 (by decide) (choices 1) [8] profile44_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [] (choices 1) [8] profile44_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile44_node1

theorem profile44 : Upper (D (n:=4) [10,16,18,19]) (R (n:=4) [10,16,18,19]) [] 2 := profile44_node0

def profile45_node3_cert : Bound 4 := { allowed := (rows 0 0 0 1), upper := (rows 9 11 13 14), lower := (rows 9 11 13 8), losses := [] }

theorem profile45_node3 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,9] 2 :=
  bound_sound (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,9] 2 profile45_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,9] 2 profile45_node3_cert).mp (by decide +kernel))

def profile45_node4_cert : Bound 4 := { allowed := (rows 0 0 1 1), upper := (rows 9 11 14 13), lower := (rows 9 11 14 8), losses := [] }

theorem profile45_node4 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,10] 2 :=
  bound_sound (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,10] 2 profile45_node4_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9,10] 2 profile45_node4_cert).mp (by decide +kernel))

def profile45_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile45_node2 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9] 2 := by
  apply routed_branch (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9] 2 (by decide) (choices 2) [9,10] profile45_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,9] (choices 2) [9,10] profile45_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile45_node3
  · exact profile45_node4

def profile45_node6_cert : Bound 4 := { allowed := (rows 0 1 0 1), upper := (rows 9 14 13 11), lower := (rows 9 14 13 8), losses := [] }

theorem profile45_node6 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12,9] 2 :=
  bound_sound (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12,9] 2 profile45_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12,9] 2 profile45_node6_cert).mp (by decide +kernel))

def profile45_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile45_node5 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12] 2 := by
  apply routed_branch (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12] 2 (by decide) (choices 2) [9] profile45_node5_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8,12] (choices 2) [9] profile45_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node6

def profile45_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile45_node1 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8] 2 := by
  apply routed_branch (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8] 2 (by decide) (choices 2) [9,12] profile45_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [8] (choices 2) [9,12] profile45_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile45_node2
  · exact profile45_node5

def profile45_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile45_node0 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [] 2 := by
  apply routed_branch (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [] 2 (by decide) (choices 1) [8] profile45_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [] (choices 1) [8] profile45_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile45_node1

theorem profile45 : Upper (D (n:=4) [10,17,17,19]) (R (n:=4) [10,17,17,19]) [] 2 := profile45_node0

def profile46_node3_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 3 14 13 13), lower := (rows 3 14 13 8), losses := [{ target := 0, region := (rows 0 6 4 8), good := (rows 2 14 14 8) }] }

theorem profile46_node3 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12,9] 2 :=
  bound_sound (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12,9] 2 profile46_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12,9] 2 profile46_node3_cert).mp (by decide +kernel))

def profile46_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node2 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12] 2 (by decide) (choices 2) [9] profile46_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2,12] (choices 2) [9] profile46_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node3

def profile46_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node1 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2] 2 (by decide) (choices 2) [12] profile46_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [2] (choices 2) [12] profile46_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node2

def profile46_node6_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 5 11 13 14), lower := (rows 5 11 13 8), losses := [{ target := 2, region := (rows 1 6 0 8), good := (rows 3 11 11 8) }] }

theorem profile46_node6 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,9] 2 :=
  bound_sound (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,9] 2 profile46_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,9] 2 profile46_node6_cert).mp (by decide +kernel))

def profile46_node8_cert : Bound 4 := { allowed := (rows 0 4 1 0), upper := (rows 5 11 14 13), lower := (rows 5 11 14 13), losses := [] }

theorem profile46_node8 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10,5] 2 :=
  bound_sound (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10,5] 2 profile46_node8_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10,5] 2 profile46_node8_cert).mp (by decide +kernel))

def profile46_node7_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node7 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10] 2 (by decide) (choices 2) [5] profile46_node7_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9,10] (choices 2) [5] profile46_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node8

def profile46_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node5 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9] 2 (by decide) (choices 2) [9,10] profile46_node5_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,9] (choices 2) [9,10] profile46_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile46_node6
  · exact profile46_node7

def profile46_node10_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 5 14 13 11), lower := (rows 5 14 13 8), losses := [{ target := 0, region := (rows 0 6 4 8), good := (rows 6 14 14 8) }] }

theorem profile46_node10 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12,9] 2 :=
  bound_sound (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12,9] 2 profile46_node10_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12,9] 2 profile46_node10_cert).mp (by decide +kernel))

def profile46_node9_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node9 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12] 2 (by decide) (choices 2) [9] profile46_node9_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4,12] (choices 2) [9] profile46_node9_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile46_node10

def profile46_node4_route : Route 4 := (fun mask => (mask,id))

theorem profile46_node4 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4] 2 (by decide) (choices 2) [9,12] profile46_node4_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [4] (choices 2) [9,12] profile46_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile46_node5
  · exact profile46_node9

def profile46_node0_route : Route 4 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile46_node0 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [] 2 := by
  apply routed_branch (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [] 2 (by decide) (choices 1) [2,4] profile46_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [] (choices 1) [2,4] profile46_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile46_node1
  · exact profile46_node4

theorem profile46 : Upper (D (n:=4) [10,17,18,18]) (R (n:=4) [10,17,18,18]) [] 2 := profile46_node0

def profile47_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile47_node2 : Upper (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2,1] 2 := by
  apply routed_branch (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2,1] 2 (by decide) (choices 2) [] profile47_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2,1] (choices 2) [] profile47_node2_route).mp (by decide +kernel))
  intro mask member
  simp at member

def profile47_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile47_node1 : Upper (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2] 2 := by
  apply routed_branch (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2] 2 (by decide) (choices 1) [1] profile47_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [2] (choices 1) [1] profile47_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node2

def profile47_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile47_node0 : Upper (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [] 2 := by
  apply routed_branch (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [] 2 (by decide) (choices 1) [2] profile47_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [] (choices 1) [2] profile47_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile47_node1

theorem profile47 : Upper (D (n:=4) [11,11,16,25]) (R (n:=4) [11,11,16,25]) [] 2 := profile47_node0

def profile48_node3_cert : Bound 4 := { allowed := (rows 0 0 0 3), upper := (rows 3 3 7 15), lower := (rows 3 3 7 8), losses := [] }

theorem profile48_node3 : Upper (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1,3] 2 :=
  bound_sound (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1,3] 2 profile48_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1,3] 2 profile48_node3_cert).mp (by decide +kernel))

def profile48_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile48_node2 : Upper (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1] 2 := by
  apply routed_branch (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1] 2 (by decide) (choices 2) [3] profile48_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2,1] (choices 2) [3] profile48_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node3

def profile48_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile48_node1 : Upper (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2] 2 := by
  apply routed_branch (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2] 2 (by decide) (choices 1) [1] profile48_node1_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [2] (choices 1) [1] profile48_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node2

def profile48_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile48_node0 : Upper (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [] 2 := by
  apply routed_branch (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [] 2 (by decide) (choices 1) [2] profile48_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [] (choices 1) [2] profile48_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile48_node1

theorem profile48 : Upper (D (n:=4) [11,11,17,24]) (R (n:=4) [11,11,17,24]) [] 2 := profile48_node0

def profile49_node3_cert : Bound 4 := { allowed := (rows 0 0 0 1), upper := (rows 9 11 13 13), lower := (rows 9 11 13 8), losses := [] }

theorem profile49_node3 : Upper (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9,9] 2 :=
  bound_sound (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9,9] 2 profile49_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9,9] 2 profile49_node3_cert).mp (by decide +kernel))

def profile49_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile49_node2 : Upper (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9] 2 := by
  apply routed_branch (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9] 2 (by decide) (choices 2) [9] profile49_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8,9] (choices 2) [9] profile49_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node3

def profile49_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile49_node1 : Upper (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8] 2 := by
  apply routed_branch (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8] 2 (by decide) (choices 2) [9] profile49_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [8] (choices 2) [9] profile49_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node2

def profile49_node0_route : Route 4 := (fun mask => (mask,id))

theorem profile49_node0 : Upper (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [] 2 := by
  apply routed_branch (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [] 2 (by decide) (choices 1) [8] profile49_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [] (choices 1) [8] profile49_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile49_node1

theorem profile49 : Upper (D (n:=4) [11,16,17,19]) (R (n:=4) [11,16,17,19]) [] 2 := profile49_node0

def profile50_node3_cert : Bound 4 := { allowed := (rows 0 0 0 5), upper := (rows 5 11 13 13), lower := (rows 5 11 13 8), losses := [{ target := 2, region := (rows 1 6 0 8), good := (rows 3 11 11 8) }] }

theorem profile50_node3 : Upper (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9,9] 2 :=
  bound_sound (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9,9] 2 profile50_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9,9] 2 profile50_node3_cert).mp (by decide +kernel))

def profile50_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile50_node2 : Upper (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9] 2 := by
  apply routed_branch (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9] 2 (by decide) (choices 2) [9] profile50_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4,9] (choices 2) [9] profile50_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node3

def profile50_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile50_node1 : Upper (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4] 2 := by
  apply routed_branch (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4] 2 (by decide) (choices 2) [9] profile50_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [4] (choices 2) [9] profile50_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node2

def profile50_node0_route : Route 4 := (fun mask => match mask with | 8 => (4,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile50_node0 : Upper (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [] 2 := by
  apply routed_branch (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [] 2 (by decide) (choices 1) [4] profile50_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [] (choices 1) [4] profile50_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile50_node1

theorem profile50 : Upper (D (n:=4) [11,16,18,18]) (R (n:=4) [11,16,18,18]) [] 2 := profile50_node0

def profile51_node3_cert : Bound 4 := { allowed := (rows 0 0 0 1), upper := (rows 3 11 13 13), lower := (rows 3 11 13 8), losses := [] }

theorem profile51_node3 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9,9] 2 :=
  bound_sound (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9,9] 2 profile51_node3_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9,9] 2 profile51_node3_cert).mp (by decide +kernel))

def profile51_node2_route : Route 4 := (fun mask => (mask,id))

theorem profile51_node2 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9] 2 := by
  apply routed_branch (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9] 2 (by decide) (choices 2) [9] profile51_node2_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2,9] (choices 2) [9] profile51_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node3

def profile51_node1_route : Route 4 := (fun mask => (mask,id))

theorem profile51_node1 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2] 2 := by
  apply routed_branch (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2] 2 (by decide) (choices 2) [9] profile51_node1_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [2] (choices 2) [9] profile51_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node2

def profile51_node6_cert : Bound 4 := { allowed := (rows 0 8 0 1), upper := (rows 9 7 13 11), lower := (rows 9 7 13 8), losses := [] }

theorem profile51_node6 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5,9] 2 :=
  bound_sound (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5,9] 2 profile51_node6_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5,9] 2 profile51_node6_cert).mp (by decide +kernel))

def profile51_node5_route : Route 4 := (fun mask => (mask,id))

theorem profile51_node5 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5] 2 := by
  apply routed_branch (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5] 2 (by decide) (choices 2) [9] profile51_node5_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,5] (choices 2) [9] profile51_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile51_node6

def profile51_node7_cert : Bound 4 := { allowed := (rows 0 0 1 1), upper := (rows 9 11 7 15), lower := (rows 9 11 4 8), losses := [{ target := 3, region := (rows 1 2 6 0), good := (rows 1 7 4 0) }] }

theorem profile51_node7 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,9] 2 :=
  bound_sound (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,9] 2 profile51_node7_cert
    ((SmallBoolean.boundCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8,9] 2 profile51_node7_cert).mp (by decide +kernel))

def profile51_node4_route : Route 4 := (fun mask => (mask,id))

theorem profile51_node4 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8] 2 := by
  apply routed_branch (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8] 2 (by decide) (choices 2) [5,9] profile51_node4_route
    (by change RowCover 4 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [8] (choices 2) [5,9] profile51_node4_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node5
  · exact profile51_node7

def profile51_node0_route : Route 4 := (fun mask => match mask with | 4 => (2,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile51_node0 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [] 2 := by
  apply routed_branch (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [] 2 (by decide) (choices 1) [2,8] profile51_node0_route
    (by change RowCover 4 1 (choices 1); exact cover ⟨1,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [] (choices 1) [2,8] profile51_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile51_node1
  · exact profile51_node4

theorem profile51 : Upper (D (n:=4) [11,17,17,18]) (R (n:=4) [11,17,17,18]) [] 2 := profile51_node0

def catalogue : List (List Nat) := [[2,9,25,27],[2,9,26,26],[2,10,24,27],[2,10,25,26],[2,11,24,26],[2,11,25,25],[2,16,18,27],[2,16,19,26],[2,17,17,27],[2,17,18,26],[2,17,19,25],[2,18,18,25],[2,18,19,24],[3,9,24,27],[3,9,25,26],[3,10,24,26],[3,10,25,25],[3,11,24,25],[3,16,17,27],[3,16,18,26],[3,16,19,25],[3,17,17,26],[3,17,18,25],[3,17,19,24],[3,18,18,24],[9,9,18,27],[9,9,19,26],[9,10,17,27],[9,10,18,26],[9,10,19,25],[9,11,16,27],[9,11,17,26],[9,11,18,25],[9,11,19,24],[9,16,19,19],[9,17,18,19],[9,18,18,18],[10,10,16,27],[10,10,17,26],[10,10,18,25],[10,10,19,24],[10,11,16,26],[10,11,17,25],[10,11,18,24],[10,16,18,19],[10,17,17,19],[10,17,18,18],[11,11,16,25],[11,11,17,24],[11,16,17,19],[11,16,18,18],[11,17,17,18]]

theorem catalogue_eq : profiles 4 4 0 7 7=catalogue := by decide +kernel

theorem profile_upper (xs : List Nat) (member : xs∈profiles 4 4 0 7 7) :
    Upper (n:=4) (D xs) (R xs) [] 2 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0
  · exact profile1
  · exact profile2
  · exact profile3
  · exact profile4
  · exact profile5
  · exact profile6
  · exact profile7
  · exact profile8
  · exact profile9
  · exact profile10
  · exact profile11
  · exact profile12
  · exact profile13
  · exact profile14
  · exact profile15
  · exact profile16
  · exact profile17
  · exact profile18
  · exact profile19
  · exact profile20
  · exact profile21
  · exact profile22
  · exact profile23
  · exact profile24
  · exact profile25
  · exact profile26
  · exact profile27
  · exact profile28
  · exact profile29
  · exact profile30
  · exact profile31
  · exact profile32
  · exact profile33
  · exact profile34
  · exact profile35
  · exact profile36
  · exact profile37
  · exact profile38
  · exact profile39
  · exact profile40
  · exact profile41
  · exact profile42
  · exact profile43
  · exact profile44
  · exact profile45
  · exact profile46
  · exact profile47
  · exact profile48
  · exact profile49
  · exact profile50
  · exact profile51
theorem upper (E : Graph (Fin 4)) (loops : Loopless E) (budget : arcCount E=7)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x) : score E≤2 := by
  have od (x) : SparseSupport.outdegree E x<4 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<4 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 4).map (SparseSupport.outdegree E)).sum=7 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 4).map (SparseSupport.indegree E)).sum=7 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    (by decide) od idg degree td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetSevenOrder4
